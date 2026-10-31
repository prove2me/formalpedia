-- Prove2me | Theorems.Thm_PersuasionNetworks_lemma_7
-- name    : PersuasionNetworks.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:30:27.445252+00:00
-- url     : https://prove2.me/theorems/eb91246a-17d8-4321-893d-049f27c1cf1d
-- title:
--   Lemma 7 — the homotopy (20) stays feasible up to the first new binding constraint
-- statement:
--   Let $(p^\star,z^\star)$ be feasible in (OPT) with C1 and C2, let $j\in[m]$, let $(\bar p,\bar z)$ be an optimal solution of (19) with $i=j$, and for $\alpha\in[0,1]$ let
--   $$
--   \hat p_k=\alpha\bar p_k+(1-\alpha)p^\star_k,\quad \hat z_k=\alpha\bar z_k+(1-\alpha)z^\star_k\quad(k\in\bar L_j),\qquad \hat p_k=p^\star_k,\ \hat z_k=z^\star_k\quad\text{otherwise}.
--   $$
--
--   (a) For any $\alpha\in[0,1]$, $(\hat p,\hat z)$ satisfies the last three constraints of (OPT).
--
--   (b) Let $\alpha_0\in(0,1]$ be the smallest $\alpha$ for which the first constraint of (OPT) is binding under $(\hat p,\hat z)$ for some $L\notin\{L_i\}_{i\in[m]}$, and $\alpha_0=1$ if there is no such $\alpha$. For $\alpha\in[0,\alpha_0]$, $(\hat p,\hat z)$ still satisfies the first constraint, this constraint remains binding for $L\in\{L_i\}_{i\in[m]}$, and $(\hat p,\hat z)$ is feasible in (OPT).
--
--   This is the structural step of the proof that C3 can be enforced.
--
--   Differences from the source:
--   - reading: L ⊂ 𝒮 in (b) → initial segments L = [k′]; reason: the proof says "of the form {0, 1, …, k′} ∩ 𝒮", p.45, and binding is defined only for those on p.18
--   - reading: b_k p_k ≤ z_k for k ∈ L̄_i ∩ P in (19) → the guard b_k ≠ −∞; reason: footnote 17 omits this constraint of (OPT) at b_K = −∞, and (19) is built from (OPT)
--   - encoding: the index i ∈ [m] and the sets L_i → a pair (e', e) of consecutive binding indices; reason: L_i = [e_i] for e_0 = 0 < e_1 < …; same data
--   - encoding: "let α′ be the smallest α …; if no such α′ exists, set α′ = 1" → ∃ α₀ in (0, 1] that is the least element of that set, or that set is empty and α₀ = 1; reason: this pins α₀ uniquely, and the clause also says the minimum exists
-- source:
--   Candogan, Persuasion in Networks: Public Signals and Cores, SSRN 3346144 (preprint), https://ssrn.com/abstract=3346144, Lemma 7, p.44

import Mathlib
import Definitions.Def_PersuasionNetworks_OPT
import Definitions.Def_PersuasionNetworks_Mechanism

open MeasureTheory ProbabilityTheory

namespace PersuasionNetworks

/-- **Lemma 7**, Candogan, SSRN 3346144 (preprint), p.44 (proof pp.44–45). Let `(p⋆, z⋆)` be feasible in (OPT) with C1 and
C2, let `(e', e)` be its block number `j`, let `(p̄, z̄)` be optimal in (19) with `i = j`, and let
`(p̂, ẑ)` be the homotopy (20).

(a) For any `α ∈ [0, 1]`, `(p̂, ẑ)` satisfies the last three constraints of (OPT).

(b) Let `α₀ ∈ (0, 1]` be the smallest `α` for which `(p̂, ẑ)` binds the first constraint of (OPT) for
some `L ∉ {L_i}`, and `α₀ = 1` if there is no such `α`. For `α ∈ [0, α₀]`, `(p̂, ẑ)` still satisfies
the first constraint and it remains binding for `L ∈ {L_i}`. Hence `(p̂, ẑ)` is feasible in (OPT).

**Formalization Note.** "`L ⊂ 𝒮`" in (b) means initial segments `L = [k']`, as in the proof
("of the form `{0, 1, …, k'} ∩ 𝒮`", p.45), and "binding" is defined only for those on p.18. The
existential over `α₀` is pinned by its disjunction: a least element is unique. -/
theorem lemma_7 (μ : Measure ℝ) [IsProbabilityMeasure μ] (𝒯 : Set ℝ) (K : ℕ) (b : ℕ → EReal) (r : ℕ → ℝ)
    (hμ : IsState μ 𝒯) (hstep : IsStepPayoff 𝒯 K b r)
    (pS zS pB zB : ℕ → ℝ) (e' e : ℕ)
    (hfeas : IsFeasible μ 𝒯 K b pS zS) (hC1 : C1 μ 𝒯 K pS zS) (hC2 : C2 K pS zS)
    (hblock : IsBlock μ 𝒯 K pS zS e' e)
    (hopt : IsAuxOptimal μ 𝒯 b r pS e' e pB zB) :
    (∀ α ∈ Set.Icc (0 : ℝ) 1, LastConstraints K b (blockMix e' e α pB pS) (blockMix e' e α zB zS)) ∧
    ∃ α₀ ∈ Set.Ioc (0 : ℝ) 1,
      (IsLeast {α ∈ Set.Ioc (0 : ℝ) 1 | ∃ k' ∈ Finset.Icc 1 K, ¬ IsBinding μ 𝒯 pS zS k' ∧
          IsBinding μ 𝒯 (blockMix e' e α pB pS) (blockMix e' e α zB zS) k'} α₀ ∨
        ({α ∈ Set.Ioc (0 : ℝ) 1 | ∃ k' ∈ Finset.Icc 1 K, ¬ IsBinding μ 𝒯 pS zS k' ∧
          IsBinding μ 𝒯 (blockMix e' e α pB pS) (blockMix e' e α zB zS) k'} = ∅ ∧ α₀ = 1)) ∧
      ∀ α ∈ Set.Icc (0 : ℝ) α₀,
        FirstConstraint μ 𝒯 K (blockMix e' e α pB pS) (blockMix e' e α zB zS) ∧
        (∀ k' ∈ Finset.Icc 1 K, IsBinding μ 𝒯 pS zS k' →
          IsBinding μ 𝒯 (blockMix e' e α pB pS) (blockMix e' e α zB zS) k') ∧
        IsFeasible μ 𝒯 K b (blockMix e' e α pB pS) (blockMix e' e α zB zS) := by sorry

end PersuasionNetworks
