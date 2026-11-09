-- Prove2me | Theorems.Thm_SemAC02_theorem_8_1_lifted_lower_bound
-- name    : SemAC02.theorem_8_1_lifted_lower_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:29:41.650958+00:00
-- url     : https://prove2.me/theorems/6bdf8095-6943-48f6-950f-563335564ab4
-- title:
--   Theorem 8.1 — lifted CNFs need semantic depth-$d$ AC0[2]-Frege size $\exp(\Omega_d(\ln n(\ln\Delta_n)^{1/(d-1)}))$
-- statement:
--   Fix $d\ge2$, a constant $w_0$ and $C>0$. Let $F_n$ be an unsatisfiable CNF on $n$ variables of maximum clause width at most $w_0$, with $\Delta_n=\deg_{\mathrm{PC}}(F_n)\ge n^C$. There is a gadget $g$ (in the sense of §8.1) such that
--
--   1. $\mathrm{Lift}_g(F_n)$ has total circuit size $N=n^{O_{d,w_0}(1)}$;
--   2. every semantic depth-$d$ AC0[2]-Frege refutation of $\mathrm{Lift}_g(F_n)$ has size
--   $$
--   \exp\Bigl(\Omega_d\bigl(\ln n\,(\ln\Delta_n)^{1/(d-1)}\bigr)\Bigr);
--   $$
--   3. $\mathrm{Lift}_g(F_n)$ has a polynomial-size semantic depth-$(d+1)$ AC0-Frege refutation (all gates AND/OR).
--
--   Precisely: for every $d\ge2$ there is $c>0$; for every $w_0$ there is $K$; for every $C>0$ there is $n_0$; and for all $n\ge n_0$, every such $F_n$ and every $\Delta$ with $n^C\le\Delta\le\deg_{\mathrm{PC}}(F_n)$ there is a gadget $g$ with $\mathrm{size}(\mathrm{Lift}_g(F_n))\le n^K$, every depth-$d$ refutation of size at least $\exp\bigl(c\ln n(\ln\Delta)^{1/(d-1)}\bigr)$, and a depth-$(d+1)$ AND/OR refutation of size at most $n^K$.
--
--   The lower and upper bounds together separate depth $d$ from depth $d+1$ for semantic AC0[2]-Frege on CNF-like inputs of polynomial size; applied to random 3-CNFs they give lower bounds $\exp(\Omega_d((\log N)^{d/(d-1)}))$.
--
--   Differences from the source:
--   - encoding: Ω_d(·), n^{O_{d,w₀}(1)}, "polynomial-size", the implicit "for n large" → ∃ c > 0 depending on d; ∃ K depending on d, w₀ (one exponent for both size bounds); ∃ n₀ depending on d, w₀, C; quantified in that order; reason: standard reading; c is chosen before w₀ and C, and K before C, as the subscripts say
--   - encoding: Δ_n = deg_PC(F_n) ≥ n^C, the bound in terms of Δ_n → for every Δ with n^C ≤ Δ and PCDegreeAtLeast F Δ, the bound with Δ; reason: taking Δ = deg_PC(F_n) gives the printed statement, and the printed statement implies this one because the bound increases with Δ
--   - encoding: "there exists a gadget g"; Lift_g(F_n); circuits and sizes → IsGadget d g (§8.1 conditions, normal form included), lift g F, Circ trees with List children, famSize / proofSize counting distinct subterms; reason: the paper's circuits are list presentations in normal form; normalising never increases depth or size, so lower bounds over list refutations are the paper's and the constructed lift and refutation are paper objects
--   - encoding: CNF on n variables of width ≤ w₀ (clauses 1 ≤ |I| ≤ w₀ in §8.1) → LiftSAParity.CNF (Fin n) with every clause of size ≤ w₀; reason: an empty clause gives a degree-0 PC refutation, which the hypothesis n^C ≤ Δ ≤ deg_PC excludes for n ≥ 1; same instances
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), Theorem 8.1, p.62 (PDF p.64)

import Mathlib
import Definitions.Def_SemAC02_Circ
import Definitions.Def_SemAC02_IsSemRefutation
import Definitions.Def_SemAC02_IsGadget
import Definitions.Def_SemAC02_lift
import Definitions.Def_SemAC02_PCDegreeAtLeast
import Definitions.Def_LiftSAParity_CNF

namespace SemAC02

/-- **Theorem 8.1 (Size lower bound for `Lift_g(F_n)`)** (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret, *Hard Instances for Strong Semantic Proof
Systems*, manuscript (STOC 2027 submission), Theorem 8.1, p.62):
fix `d ≥ 2`, a constant `w₀`, and `C > 0`. Let `F_n` be an unsatisfiable CNF on `n` variables of
maximum clause width at most `w₀`, with `Δ_n = deg_PC(F_n) ≥ n^C`. There exists a gadget `g` such
that `Lift_g(F_n)` has total circuit size `N = n^{O_{d,w₀}(1)}`, and every semantic depth-`d`
AC0[2]-Frege refutation of `Lift_g(F_n)` has size `exp(Ω_d(ln n (ln Δ_n)^{1/(d−1)}))`. The formula
has a polynomial-size semantic depth-`(d + 1)` AC0-Frege refutation.

**Formalization Note**
1. Constants: `Ω_d` is one `c > 0` depending on `d` only; `O_{d,w₀}(1)` and "polynomial-size" are
   one exponent `K` depending on `d, w₀`; the bounds hold for `n ≥ n₀(d, w₀, C)`.
2. `Δ_n = deg_PC(F_n) ≥ n^C` is stated for every `Δ` with `n^C ≤ Δ` and `deg_PC(F_n) ≥ Δ`
   (`PCDegreeAtLeast`); taking `Δ = deg_PC(F_n)` gives the printed form, and the bound increases
   with `Δ`.
3. A gadget is a circuit satisfying the conditions of §8.1 (`IsGadget d g`, normal form
   included); `Lift_g(F_n)` is Definition 8.2; circuits are lists-of-children trees; sizes count
   distinct subcircuits (`famSize`, `proofSize`). AC0-Frege: every line is an AND/OR circuit. -/
theorem theorem_8_1_lifted_lower_bound :
    ∀ d : ℕ, 2 ≤ d → ∃ c : ℝ, 0 < c ∧ ∀ w₀ : ℕ, ∃ K : ℕ, ∀ C : ℝ, 0 < C → ∃ n₀ : ℕ,
      ∀ n : ℕ, n₀ ≤ n → ∀ F : LiftSAParity.CNF (Fin n), ¬ LiftSAParity.Satisfiable F →
        (∀ Cl ∈ F, Cl.card ≤ w₀) → ∀ Δ : ℕ, (n : ℝ) ^ C ≤ (Δ : ℝ) → PCDegreeAtLeast F Δ →
          ∃ (m : ℕ) (g : Circ (Fin m)), IsGadget d g ∧
            famSize (lift g F) ≤ n ^ K ∧
            (∀ π : List (Circ (Fin n × Fin m)),
              IsSemRefutation d (lift g F : Set (Circ (Fin n × Fin m))) π →
                Real.exp (c * Real.log n * (Real.log Δ) ^ ((1 : ℝ) / ((d : ℝ) - 1))) ≤
                  (proofSize π : ℝ)) ∧
            (∃ π : List (Circ (Fin n × Fin m)),
              IsSemRefutation (d + 1) (lift g F : Set (Circ (Fin n × Fin m))) π ∧
                (∀ A ∈ π, NoXor A) ∧ proofSize π ≤ n ^ K) := by sorry

end SemAC02
