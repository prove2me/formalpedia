-- Prove2me | Theorems.Thm_VertexSampleCSP_proposition_C_2
-- name    : VertexSampleCSP.proposition_C_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:55:45.433628+00:00
-- url     : https://prove2.me/theorems/1ae736ba-2e66-4e3e-a58e-fac32c181f01
-- title:
--   Proposition C.2, p.16 — one step: $\mathbb E|\rho^{-r}\mathrm{OPT}(\mathcal I[S])-\mathrm{OPT}(\mathcal I)|\le\frac{4(2^r-1)}{\sqrt{r\cdot r!}}N^{(r-2)/2}\Gamma(\mathcal I)$
-- statement:
--   Let $\mathcal I$ be an instance of arity $r$ with real payoffs on $N$ variables and let $\tfrac12\le\rho\le1$.
--
--   1. If $S$ contains every variable independently with probability $\rho$, then
--
--   $$\mathbb E\big|\rho^{-r}\mathrm{OPT}(\mathcal I[S])-\mathrm{OPT}(\mathcal I)\big|\le\frac{4(2^r-1)}{\sqrt{r\cdot r!}}N^{(r-2)/2}\Gamma(\mathcal I).$$
--
--   2. For $\rho=\tfrac12$ in that model, the factor $4$ improves to $2\sqrt2$.
--   3. If $S$ is a uniformly random subset of size $\rho N$, the same holds with the factor $4\sqrt2$ in place of $4$.
--
--   Halving the sample once costs an error controlled by $\Gamma$ alone. The chain of samples in Theorem C.4 applies this to each step.
--
--   **Formalization Note** $N^{(r-2)/2}$ is a real power, equal to $1$ for $r=2$.
--
--   Differences from the source:
--
--   - encoding: arity r ≥ 2 of the section → hypothesis 2 ≤ r; reason: the standing assumption of Appendix A
--   - encoding: alphabet [q] = {1, …, q} → q ≥ 1 is a hypothesis and the alphabet is Fin q; reason: q = 0 leaves the optimum and the polytopes undefined, so this excludes only undefined cases
--   - encoding: I[S] is the instance on S → I.sub S on the subtype ↥S; reason: same instance, written in a type with |S| variables
--   - encoding: a uniformly random subset of size ρN → N′ : ℕ with (N′ : ℝ) = ρN; reason: such a subset exists exactly when ρN is an integer
--   - encoding: E over the random subset → the finite averages bernAvg and unifAvg; reason: same expectations
-- source:
--   Chang, Optimal Vertex Sampling for Constraint Satisfaction Problems, STOC 2027 submission (manuscript sha256 1e0edd23…), Proposition C.2, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_VertexSampleCSP_Instance
import Definitions.Def_VertexSampleCSP_OPT
import Definitions.Def_VertexSampleCSP_Instance_sub
import Definitions.Def_VertexSampleCSP_Instance_Gamma
import Definitions.Def_VertexSampleCSP_bernAvg
import Definitions.Def_VertexSampleCSP_unifAvg

namespace VertexSampleCSP

/-- **Proposition C.2 (One step).** Chang, *Optimal Vertex Sampling for Constraint Satisfaction
Problems*, STOC 2027 submission (manuscript sha256 1e0edd23…), Proposition C.2, p.16 (PDF p.18):
"Let I be an instance of arity r on N variables and let 1/2 ≤ ρ ≤ 1.
(a) If S contains every variable independently with probability ρ, then
E |ρ^{−r} OPT(I[S]) − OPT(I)| ≤ (4(2^r − 1)/√(r · r!)) N^{(r−2)/2} Γ(I), and for ρ = 1/2 the
factor 4 improves to 2√2.
(b) If S is a uniformly random subset of size ρN, then the same holds with the factor 4√2 in place
of 4."

For an instance `I` with real payoffs on `N = |V|` variables:
1. for `1/2 ≤ ρ ≤ 1` and a Bernoulli(`ρ`) subset `S`:
   `E|ρ^{−r} OPT(I[S]) − OPT(I)| ≤ (4(2^r − 1)/√(r·r!)) N^{(r−2)/2} Γ(I)`;
2. for `ρ = 1/2` and a Bernoulli(`1/2`) subset: the same with `2√2` in place of `4`;
3. for `1/2 ≤ ρ ≤ 1` with `ρN` an integer `N′`, and a uniformly random `N′`-subset `S`: the same with
   `4√2` in place of `4`.

**Formalization Note.** `I[S]` is the instance on the subtype `↥S` (so it has `|S|` variables).
Payoffs are arbitrary reals; `[q]` is `Fin q` with `q ≥ 1`. "A subset of size ρN" requires `ρN` to
be an integer: the statement quantifies over `N′ : ℕ` with `N′ = ρN`. `N^{(r−2)/2}` is a real power
(equal to `1` for `r = 2`). -/
theorem proposition_C_2 {V : Type*} [Fintype V] [DecidableEq V] {r q : ℕ} (hr : 2 ≤ r)
    (hq : 0 < q) (I : Instance V r q) :
    (∀ ρ : ℝ, 1 / 2 ≤ ρ → ρ ≤ 1 →
      bernAvg ρ (fun S => |(ρ ^ r)⁻¹ * OPT (I.sub S) - OPT I|) ≤
        4 * (2 ^ r - 1) / Real.sqrt (r * (r.factorial : ℝ)) *
          (Fintype.card V : ℝ) ^ (((r : ℝ) - 2) / 2) * I.Gamma) ∧
    bernAvg (1 / 2 : ℝ) (fun S => |(((1 : ℝ) / 2) ^ r)⁻¹ * OPT (I.sub S) - OPT I|) ≤
        2 * Real.sqrt 2 * (2 ^ r - 1) / Real.sqrt (r * (r.factorial : ℝ)) *
          (Fintype.card V : ℝ) ^ (((r : ℝ) - 2) / 2) * I.Gamma ∧
    (∀ ρ : ℝ, 1 / 2 ≤ ρ → ρ ≤ 1 → ∀ N' : ℕ, (N' : ℝ) = ρ * Fintype.card V →
      unifAvg N' (fun S => |(ρ ^ r)⁻¹ * OPT (I.sub S) - OPT I|) ≤
        4 * Real.sqrt 2 * (2 ^ r - 1) / Real.sqrt (r * (r.factorial : ℝ)) *
          (Fintype.card V : ℝ) ^ (((r : ℝ) - 2) / 2) * I.Gamma) := by sorry

end VertexSampleCSP
