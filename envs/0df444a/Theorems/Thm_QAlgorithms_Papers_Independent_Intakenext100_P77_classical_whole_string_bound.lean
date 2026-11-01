-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P77_classical_whole_string_bound
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P77.classical_whole_string_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:04:57.383996+00:00
-- url     : https://prove2.me/theorems/5c4f4850-45ea-4b99-a7a7-930f3378bdb5
-- title:
--   Full-string classical information
-- statement:
--   Let $m\ge1$ and let $A_1,\ldots,A_m$ be jointly independent random variables with finite alphabets on a normalized finite probability space. Let $E$ be any finite-valued random variable on the same space; it may depend arbitrarily on the family. Information is Shannon mutual information in bits. Write $A_{<i}$ for preceding coordinates and $A_{\ne i}$ for all other coordinates.
--
--   The full-string information satisfies
--
--   $$I(A_1,\ldots,A_m;E)\le m\max_{1\le i\le m}I(A_i;E\mid A_{\ne i}).$$
--
--   The maximum is over a nonempty finite index set. This provides the factor $m$ in the whole-key bound.
-- source:
--   A Proof of the Security of Quantum Key Distribution, arXiv:quant-ph/9912053v1, PDF p. 24, Theorem H.1: full-string classical information

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

/-- Theorem H.1, PDF p.24: full independent-string information is bounded by
m times the maximum coordinate information with all other coordinates disclosed. -/
theorem classical_whole_string_bound {Omega E : Type}
    [Fintype Omega] [Fintype E] {m : ℕ} (hm : 1 ≤ m)
    {A : Fin m → Type} [∀ i, Fintype (A i)] (p : Law Omega)
    (key : (i : Fin m) → Omega → A i) (eve : Omega → E)
    (hind : JointIndependent p.prob key) :
    classicalMutualInfo p.prob (fun w i => key i w) eve ≤
      m * coordinateMaximum p.prob key eve := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P77

end
