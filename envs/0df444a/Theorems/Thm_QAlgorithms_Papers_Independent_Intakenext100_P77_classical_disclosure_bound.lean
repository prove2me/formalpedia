-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P77_classical_disclosure_bound
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P77.classical_disclosure_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:05:52.126612+00:00
-- url     : https://prove2.me/theorems/a7d04d8a-2f1e-4789-ba9f-53169b32a30c
-- title:
--   Maximum over disclosed outcomes
-- statement:
--   Let $m\ge1$ and let $A_1,\ldots,A_m$ be jointly independent random variables with finite alphabets on a normalized finite probability space. Let $E$ be any finite-valued random variable on the same space; it may depend arbitrarily on the family. Information is Shannon mutual information in bits. Write $A_{<i}$ for preceding coordinates and $A_{\ne i}$ for all other coordinates.
--
--   Maximizing over coordinates and positive-probability outcomes of the other coordinates gives
--
--   $$I(A_1,\ldots,A_m;E)\le m\max_{i,\,a:\Pr[A_{\ne i}=a]>0}I(A_i;E\mid A_{\ne i}=a).$$
--
--   The finite maximum is nonempty under normalization. Null outcomes do not define conditional experiments. This permits a pointwise bound after all other key bits are disclosed.
-- source:
--   A Proof of the Security of Quantum Key Distribution, arXiv:quant-ph/9912053v1, PDF p. 24, Lemma H.2: maximum over disclosed outcomes

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

/-- Lemma H.2, PDF p.24: maximize additionally over positive-probability
outcomes of the other coordinates. Null outcomes are not experiments. -/
theorem classical_disclosure_bound {Omega E : Type}
    [Fintype Omega] [Fintype E] {m : ℕ} (hm : 1 ≤ m)
    {A : Fin m → Type} [∀ i, Fintype (A i)] (p : Law Omega)
    (key : (i : Fin m) → Omega → A i) (eve : Omega → E)
    (hind : JointIndependent p.prob key) :
    classicalMutualInfo p.prob (fun w i => key i w) eve ≤
      m * disclosureMaximum p.prob key eve := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P77

end
