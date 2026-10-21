-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P29_canonical_right_covariance
-- name    : QAlgorithms.Papers.Independent.Next46.P29.canonical_right_covariance
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T14:15:56.202755+00:00
-- url     : https://prove2.me/theorems/8c44748c-f913-4d87-aa44-9e86982c00fa
-- title:
--   Encoding intertwines the constructed right action
-- statement:
--   Use the paired canonical token $e$ in the restricted finite token space for a compact Lie group $G$, with normalized Haar measure. Let $U_S$ be any continuous unitary message representation of positive dimension. Construct $V_R(h)=\bigoplus_q I_{M_q}\otimes\overline{U_q(h)}$ in the same paired bases used for $e$, and let $|g\rangle=U_R(g)|e\rangle$. Then
--
--   $$V_R(h)|g\rangle=|gh^{-1}\rangle,\qquad (V_R(h)\otimes I_S)\mathcal E(\rho)(V_R(h)^\dagger\otimes I_S)=\mathcal E\bigl(U_S(h)\rho U_S(h)^\dagger\bigr)$$
--
--   for all $g,h\in G$ and every message density operator $\rho$. This implements changes of the relational message using an action constructed entirely on the token. The constructed left and right token actions commute for every pair of group elements.
-- source:
--   Quantum communication using a bounded-size quantum reference frame, arXiv:0812.5040v2, PDF p. 5, §II.B: encoding intertwines the right action, Eq.(25)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P29

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Manifold ContDiff Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Next46.P29

open QAlgorithms.Papers.Independent.Information100.P56 (IsIrreducible)

open QAlgorithms.Papers.Independent.Information100.P63 (mixed)

open QAlgorithms.Papers.Independent.Information100.P34 (dephasing)

open QAlgorithms.Papers.Independent.Information100.P71 (IsSubchannel)

attribute [local instance] Classical.decEq Classical.propDecidable

section GeneralResults

variable {G : Type*} [Group G] [TopologicalSpace G] [hTop : IsTopologicalGroup G]
  [hCompact : CompactSpace G] [hT2 : T2Space G] [MeasurableSpace G] [hBorel : BorelSpace G]
  (mu : Measure G) [hHaar : Measure.IsHaarMeasure mu] [hProb : IsProbabilityMeasure mu]

include hTop hCompact hT2 hBorel hHaar hProb

/-- PDF pp.5–6, Eqs.(18),(20),(25): the constructed right action transports the
message inside the invariant encoding. No irreducibility of the message is assumed. -/
theorem canonical_right_covariance (hLie : HasLieStructure G)
    (C : CanonicalToken G) {s : ℕ} (hs : 0 < s) (U : BasedUnitaryRep G s) :
    (∀ g h, tokenLeft C g * tokenRight C h = tokenRight C h * tokenLeft C g) ∧
    (∀ g h, act (tokenRight C h) (tokenOrbit C g) = tokenOrbit C (g * h⁻¹)) ∧
    (∀ h rho, IsDensityMatrix rho →
      conjSuperop ((tokenRight C h).kronecker (1 : Matrix (Fin s) (Fin s) ℂ))
        (canonicalEncoding mu C U rho) = canonicalEncoding mu C U (conjSuperop (repMatrix U h) rho)) := by sorry

end GeneralResults

end QAlgorithms.Papers.Independent.Next46.P29

end
