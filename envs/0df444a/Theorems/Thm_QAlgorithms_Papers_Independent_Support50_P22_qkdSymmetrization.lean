-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P22_qkdSymmetrization
-- name    : QAlgorithms.Papers.Independent.Support50.P22.qkdSymmetrization
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T20:52:41.987453+00:00
-- url     : https://prove2.me/theorems/a48a008a-a833-4298-9c4e-7fd755fd7b66
-- title:
--   Public-permutation symmetrization and common relabeling
-- statement:
--   Let $d\ge1$, $n\ge0$, and let $E$ be a finite-dimensional classical-output CPTP QKD protocol with both keys, length branch, and full public transcript. Define the symmetrized channel by choosing each $p\in S_n$ with probability $1/n!$, applying its tensor permutation to the input, and recording $p$ publicly:
--   $$
--   E_{\mathrm{sym}}(X)=\frac1{n!}\sum_{p\in S_n}|p\rangle\langle p|\otimes E(P_pXP_p^\dagger).
--   $$
--   For each $\pi\in S_n$, let $K_\pi$ relabel the public permutation $p$ as $p\circ\pi$, leaving all other output registers untouched. Then $E_{\mathrm{sym}}$ and $K_\pi$ are CPTP, and
--   $$
--   K_\pi\circ E_{\mathrm{sym}}\circ\operatorname{Ad}(P_\pi)=E_{\mathrm{sym}},\qquad
--   K_\pi\circ(\operatorname{id}_{S_n}\otimes S)\circ E_{\mathrm{sym}}\circ\operatorname{Ad}(P_\pi)
--   =(\operatorname{id}_{S_n}\otimes S)\circ E_{\mathrm{sym}}.
--   $$
--   Here $S$ replaces the keys by an identical uniform pair while preserving length and transcript. This enforces the covariance needed for the QKD criterion without discarding the public permutation.
-- source:
--   Post-selection technique for quantum channels with applications to quantum cryptography, arXiv:0809.3019v1, PDF p. 3, Unnumbered public-permutation symmetrization, footnote 16

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

/-- Public-permutation symmetrization, PDF p.3 and p.4 footnote 16. Both
identities use the same relabeling, which leaves both keys unchanged.
In Theorem 1's orientation the corresponding channel is K_pi inverse. -/
theorem qkdSymmetrization (n d : ℕ) (hd : 0 < d)
    {L C : Type} [Fintype L] [DecidableEq L] [Nonempty L]
    [Fintype C] [DecidableEq C] [Nonempty C]
    (len : L → ℕ)
    (E : Matrix (Copies (Fin d) n) (Copies (Fin d) n) ℂ →ₗ[ℂ]
      Matrix (KeyOut L C len) (KeyOut L C len) ℂ)
    (hE : IsChannel E) (hclass : ClassicalOutput E) :
    IsChannel (publicSymmetrize E) ∧
    ∀ pi : Equiv.Perm (Fin n), IsChannel (relabelPublic (B := KeyOut L C len) pi) ∧
      (∀ X, relabelPublic pi (publicSymmetrize E (permuteInput pi X)) = publicSymmetrize E X) ∧
      (∀ X, relabelPublic pi
        (idTensorSuperop (R := Equiv.Perm (Fin n)) (keyReplacement len)
          (publicSymmetrize E (permuteInput pi X))) =
        idTensorSuperop (R := Equiv.Perm (Fin n)) (keyReplacement len)
          (publicSymmetrize E X)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P22

end
