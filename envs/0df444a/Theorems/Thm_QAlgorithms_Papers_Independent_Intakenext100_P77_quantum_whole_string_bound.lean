-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P77_quantum_whole_string_bound
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P77.quantum_whole_string_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:06:50.301857+00:00
-- url     : https://prove2.me/theorems/c4227d76-f747-40be-8cd0-90a033e2de71
-- title:
--   Quantum whole-key reduction
-- statement:
--   Let $m\ge1$, let $X$ have a normalized finite distribution, and let $A_1(X),\ldots,A_m(X)$ be jointly independent finite random variables. Let $\rho_x$ be a normalized finite-dimensional density matrix for every $x$. For any finite POVM $M$, let $E^M$ denote its classical outcome. Define
--
--   $$SD_{i,a}=\sup_N I(A_i;E^N\mid A_{\ne i}=a)$$
--
--   for positive-probability disclosures $a$, optimizing separately over all finite POVMs $N$. Then
--
--   $$I(A_1,\ldots,A_m;E^M)\le m\max_{i,\,a:\Pr[A_{\ne i}=a]>0}SD_{i,a}.$$
--
--   Normalized ensembles make each supremum nonempty and bounded by the corresponding entropy. No optimal measurement must attain its supremum; the statement applies to every whole-key measurement.
-- source:
--   A Proof of the Security of Quantum Key Distribution, arXiv:quant-ph/9912053v1, PDF p. 25, Appendix H.2 Eq.(33): quantum whole-key reduction

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

/-- Appendix H.2, PDF p.25, Eq.(33): any whole-key POVM is bounded by the
maximum separately optimized conditional information. No optimal POVM need
attain any accessible-information supremum. -/
theorem quantum_whole_string_bound {X Q : Type} [Fintype X] [Fintype Q]
    [DecidableEq Q] {m : ℕ} (hm : 1 ≤ m) {A : Fin m → Type}
    [∀ i, Fintype (A i)] (p : Law X) (rho : X → Matrix Q Q ℂ)
    (hrho : ∀ x, IsDensityMatrix (rho x))
    (key : (i : Fin m) → X → A i) (hind : JointIndependent p.prob key)
    (M : Measurement Q) :
    classicalMutualInfo (measuredWeights p.prob rho M) (fun z i => key i z.1) Prod.snd ≤
      m * quantumDisclosureMaximum p.prob rho key := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P77

end
