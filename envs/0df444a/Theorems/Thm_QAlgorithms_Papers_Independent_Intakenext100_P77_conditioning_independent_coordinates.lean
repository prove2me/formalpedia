-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P77_conditioning_independent_coordinates
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P77.conditioning_independent_coordinates
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:03:52.591372+00:00
-- url     : https://prove2.me/theorems/3beef833-8eb3-4a11-a6d7-a1792ee65e2b
-- title:
--   Information increases when other independent coordinates are disclosed
-- statement:
--   Let $m\ge1$ and let $A_1,\ldots,A_m$ be jointly independent random variables with finite alphabets on a normalized finite probability space. Let $E$ be any finite-valued random variable on the same space; it may depend arbitrarily on the family. Information is Shannon mutual information in bits. Write $A_{<i}$ for preceding coordinates and $A_{\ne i}$ for all other coordinates.
--
--   For each coordinate $i$,
--
--   $$I(A_i;E\mid A_{<i})\le I(A_i;E\mid A_{\ne i}).$$
--
--   Only joint independence of the key coordinates is needed. The statement supports reduction from whole-string information to single-coordinate information.
-- source:
--   A Proof of the Security of Quantum Key Distribution, arXiv:quant-ph/9912053v1, PDF p. 24, Lemma H.1: independence and conditioning

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P77

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P77

open scoped BigOperators ComplexConjugate ComplexOrder

open QAlgorithms

-- The repair instruction authorizes imports of pinned accepted definitions.
-- These are definitions only; no imported paper theorem is used here.

open QAlgorithms.Papers.Independent.Dependency50.P47 (Law)

open QAlgorithms.Papers.Independent.Information100.P04 (Measurement)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P39 (pushLaw)

open QAlgorithms.Papers.Independent.Support50.P16 (trivialMeasurement)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma H.1, PDF p.24: disclosing the remaining jointly independent
coordinates increases conditional information about one coordinate. No
independence from Eve's variable is assumed. Fin m excludes an empty index. -/
theorem conditioning_independent_coordinates {Omega E : Type}
    [Fintype Omega] [Fintype E] {m : ℕ} {A : Fin m → Type}
    [∀ i, Fintype (A i)] (p : Law Omega)
    (key : (i : Fin m) → Omega → A i) (eve : Omega → E)
    (hind : JointIndependent p.prob key) (i : Fin m) :
    averagedConditionalInfo p.prob (key i) eve (previous key i) ≤
      averagedConditionalInfo p.prob (key i) eve (others key i) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P77

end
