-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P22_deFinettiIdentities
-- name    : QAlgorithms.Papers.Independent.Support50.P22.deFinettiIdentities
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:50:10.50902+00:00
-- url     : https://prove2.me/theorems/955f7fd2-6875-45da-a276-d944de49919a
-- title:
--   Haar extension, symmetric projector, and purification
-- statement:
--   Let $d\ge1$ and $n\ge0$. Draw a Haar-random unit vector on $H\otimes K$, where $\dim H=\dim K=d$, and let $\mu$ be the induced law of its reduced density on $H$. Define $\tau_{H^n}$ by equation (1) and $\tau_{H^nK^n}$ by the Haar integral of the pure bipartite density's $n$th tensor power. Put $S=\operatorname{Sym}^n(H\otimes K)$ and $g=\binom{n+d^2-1}{n}$. If $P_S$ is the orthogonal projector onto $S$, then
--   $$
--   \operatorname{Tr}_{K^n}\tau_{H^nK^n}=\tau_{H^n},\qquad
--   \dim_{\mathbb C}S=g,\qquad \tau_{H^nK^n}=g^{-1}P_S.
--   $$
--   For any orthonormal basis $(\nu_i)_{i=1}^{\dim S}$ of $S$, identify a reference space $N$ with its coordinate copy and set
--   $$
--   |\Psi\rangle=(\dim S)^{-1/2}\sum_i|\nu_i\rangle\otimes|i\rangle_N.
--   $$
--   Then $\|\Psi\|=1$ and $\operatorname{Tr}_N|\Psi\rangle\langle\Psi|=\tau_{H^nK^n}$. These identities fix both the test state's ensemble and its normalization.
-- source:
--   Post-selection technique for quantum channels with applications to quantum cryptography, arXiv:0809.3019v1, PDF p. 2, Unnumbered setup identities: Haar extension, symmetric projector and dimension

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P22

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Support50.P22

attribute [local instance] Classical.decEq Classical.propDecidable

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Information100.P69 (diamond)

open QAlgorithms.Papers.Independent.Dependency50.P18 (ClassicalOutput)

attribute [local instance] QAlgorithms.Papers.Independent.Support50.P22.postselectionMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Support50.P22.postselectionMatrixBorelSpace

/-- Setup identities, PDF pp.1--2 and footnotes 10,12 on p.4. The states are
Haar integrals, and the dimension, normalized projector, extension, and basis
purification identities are all conclusions, not input certificates. -/
theorem deFinettiIdentities (n d : ℕ) (hd : 0 < d)
    (b : OrthonormalBasis (Fin (Module.finrank ℂ (pairedSymmetricSpace n d))) ℂ
      (pairedSymmetricSpace n d)) :
    traceRight (tauPair n d hd) = deFinettiState n d hd ∧
    Module.finrank ℂ (pairedSymmetricSpace n d) = factor n d ∧
    tauPair n d hd = ((factor n d : ℂ)⁻¹) • subspaceProjectorMatrix (pairedSymmetricSpace n d) ∧
    FinitePurification (basisPurification (pairedSymmetricSpace n d) b) (tauPair n d hd) := by sorry

end QAlgorithms.Papers.Independent.Support50.P22

end
