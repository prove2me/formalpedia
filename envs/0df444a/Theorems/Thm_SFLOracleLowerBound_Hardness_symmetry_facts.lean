-- Prove2me | Theorems.Thm_SFLOracleLowerBound_Hardness_symmetry_facts
-- name    : SFLOracleLowerBound.Hardness.symmetry_facts
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T02:27:50.254301+00:00
-- url     : https://prove2.me/theorems/9967957b-a367-49c8-b236-d502444fb70e
-- title:
--   Lemma 7 — Symmetry facts
-- statement:
--   Let $E$ be finite, $\Gamma$ a permutation group on $E$, and $r:2^E\to\mathbb R$ submodular and invariant under $\Gamma$. There is a global minimizer that is a union of orbits. For every $S\subseteq E$, the uniform group average $x=\mathbb E_\gamma\mathbf1_{\gamma S}$ satisfies
--   $$0\le x_e\le1,\qquad x_e=\frac{|S\cap\Gamma(e)|}{|\Gamma(e)|},\qquad \widehat r(x)\le r(S).$$
--   These are the minimization and Lovász-extension symmetry facts. Both clauses hold for functions with negative values and without normalization.
--
--   Differences from the source:
--   - encoding: finite ground sets and their subsets → finite types and Finset subsets; reason: bijections preserve every subset, cardinality and set operation
-- source:
--   Adam N. Elmachtoub, Bento Natura, Meike Neuwohner, Settling the Approximability of Submodular Facility Location, STOC 2027 submission #1249 (October 2026), Lemma 7(i)–(ii), p.8; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1249.pdf

import Mathlib
import Definitions.Def_SFLOracleLowerBound_Hardness_Symmetry

set_option autoImplicit false

noncomputable section

namespace SFLOracleLowerBound.Hardness

open Classical Finset MeasureTheory
open scoped ENNReal

/-- Lemma 7(i)–(ii), p.8. The function may have either sign and need not be normalized. -/

theorem symmetry_facts {E : Type} [Fintype E] [DecidableEq E]
    (Γ : Finset (Equiv.Perm E)) (hΓ : PermutationGroup Γ)
    (r : Finset E → ℝ) (hr : NonmonotoneSubmod.Shared.Submodular r)
    (hinv : InvariantFunction Γ r) :
    (∃ A : Finset E, InvariantSet Γ A ∧ ∀ B, r A ≤ r B) ∧
    ∀ S : Finset E,
      (∀ e, 0 ≤ orbitAverage Γ S e ∧ orbitAverage Γ S e ≤ 1) ∧
      (∀ e, orbitAverage Γ S e = ((S ∩ orbit Γ e).card : ℝ) / (orbit Γ e).card) ∧
      lovasz r (orbitAverage Γ S) ≤ r S := by sorry

end SFLOracleLowerBound.Hardness
