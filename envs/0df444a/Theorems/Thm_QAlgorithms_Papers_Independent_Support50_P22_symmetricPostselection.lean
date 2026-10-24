-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P22_symmetricPostselection
-- name    : QAlgorithms.Papers.Independent.Support50.P22.symmetricPostselection
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:49:21.883353+00:00
-- url     : https://prove2.me/theorems/302b300b-7470-4ac0-92f0-424c719e1f80
-- title:
--   Lemma 2: postselecting symmetric densities
-- statement:
--   Let $d=\dim H\ge1$, $K\cong H$, and $n\ge0$. Let $\tau_{H^nK^n}$ be the Haar average of $\sigma_{HK}^{\otimes n}$ over normalized pure states on $H\otimes K$, with paired copies regrouped into $H^n\otimes K^n$. Fix a normalized purification $\psi_{H^nK^nN}$ of this average. For every density matrix $\rho$ whose range lies in $\operatorname{Sym}^n(H\otimes K)$, there exists an effect $0\preceq M\preceq I_N$ such that, writing $T_M(X)=\operatorname{Tr}(XM)$,
--   $$
--   \rho=\binom{n+d^2-1}{n}\,(\operatorname{id}_{H^nK^n}\otimes T_M)(|\psi\rangle\langle\psi|).
--   $$
--   Here $T_M$ is a complex-linear completely positive, trace-nonincreasing functional with scalar codomain $\mathbb C$. The effect may depend on $\rho$, whereas the reference purification is fixed beforehand. This is the postselection interface for all densities supported on the symmetric vector subspace.
-- source:
--   Post-selection technique for quantum channels with applications to quantum cryptography, arXiv:0809.3019v1, PDF p. 2, Lemma 2: postselecting a symmetric density operator

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

/-- Lemma 2, PDF p.2. The purification is fixed before the target density.
An existential effect gives the source's complex-linear trace-nonincreasing
scalar CP operation T(X)=Tr(XM); the target equality is a conclusion. -/
theorem symmetricPostselection (n d : ℕ) (hd : 0 < d)
    {N : Type*} [Fintype N] [DecidableEq N] [Nonempty N]
    (psi : EuclideanSpace ℂ ((Copies (Fin d) n × Copies (Fin d) n) × N))
    (hpsi : FinitePurification psi (tauPair n d hd))
    (rho : Matrix (Copies (Fin d) n × Copies (Fin d) n) (Copies (Fin d) n × Copies (Fin d) n) ℂ)
    (hrho : IsDensityMatrix rho) (hsupp : RangeSupported rho (pairedSymmetricSpace n d)) :
    ∃ M : Matrix N N ℂ, IsEffect M ∧
      rho = (factor n d : ℂ) • postselect M (pureDensity psi) := by sorry

end QAlgorithms.Papers.Independent.Support50.P22

end
