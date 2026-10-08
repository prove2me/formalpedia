-- Prove2me | Theorems.Thm_TeschlQM_OneParticle_potential_relativelyCompact
-- name    : TeschlQM.OneParticle.potential_relativelyCompact
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-10-07T15:19:53.376981+00:00
-- url     : https://prove2.me/theorems/72938ebe-c4f3-4d25-91f1-efe51f4232f2
-- title:
--   Potentials in $L^\infty_\infty + L^2$ are relatively compact with respect to $H_0$
-- statement:
--   Let $n\ge1$ and $V:\mathbb R^n\to\mathbb R$. Suppose $V\in L^\infty_\infty(\mathbb R^n)$ (bounded, Borel, vanishing at infinity) if $n>3$, and $V\in L^\infty_\infty(\mathbb R^n)+L^2(\mathbb R^n)$ if $n\le3$. Then the maximally defined multiplication operator $V$ is **relatively compact** with respect to the free Schrödinger operator $H_0$: there is $z\in\rho(H_0)$ with $\operatorname{Ran}R_{H_0}(z)\subseteq\mathfrak D(V)$ and $V R_{H_0}(z)$ compact.
--
--   This is the first assertion of Teschl's Theorem 10.2. Its proof combines Lemma 7.11 (for the $L^\infty_\infty$ part) with Lemma 10.1 (for the $L^2$ part, $n\le 3$).
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, Theorem 10.2 (p. 222), first assertion; proof via Lemma 7.11 (p. 170) and Lemma 10.1 (p. 221)

import Mathlib
import Definitions.Def_TeschlQM_OneParticle_multiplicationOperator
import Definitions.Def_TeschlQM_OneParticle_freeHamiltonian
import Definitions.Def_TeschlQM_Shared_resolventSet
import Definitions.Def_TeschlQM_Shared_IsRelativelyCompact
import Definitions.Def_TeschlQM_OneParticle_IsBoundedVanishingAtInfinity

namespace TeschlQM.OneParticle

open MeasureTheory

/-- Teschl, proof of Theorem 10.2, p. 222 (via Lemma 7.11 and Lemma 10.1): if `V ∈ L^∞_∞(ℝⁿ)`
for `n > 3` and `V ∈ L^∞_∞(ℝⁿ) + L²(ℝⁿ)` for `n ≤ 3`, then the multiplication operator `V` is
relatively compact with respect to the free Schrödinger operator `H₀`. -/
theorem potential_relativelyCompact (n : ℕ) (hn : 1 ≤ n) (V : EuclideanSpace ℝ (Fin n) → ℝ)
    (hV_large : 3 < n → IsBoundedVanishingAtInfinity V)
    (hV_small : n ≤ 3 → ∃ V₁ V₂ : EuclideanSpace ℝ (Fin n) → ℝ,
      IsBoundedVanishingAtInfinity V₁ ∧ MemLp V₂ 2 volume ∧ V = V₁ + V₂) :
    TeschlQM.Shared.IsRelativelyCompact (multOp (fun x => (V x : ℂ))) (freeHamiltonian n) := by
  sorry

end TeschlQM.OneParticle
