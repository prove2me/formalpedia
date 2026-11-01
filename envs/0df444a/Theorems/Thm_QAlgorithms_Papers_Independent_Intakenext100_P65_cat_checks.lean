-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P65_cat_checks
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P65.cat_checks
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:26:13.085875+00:00
-- url     : https://prove2.me/theorems/94b9f12c-f89a-49b3-a951-e277ba818da0
-- title:
--   Cat normalization, annihilation eigenoperator and loss syndromes
-- statement:
--   Let $S\ge0$ be an integer and $a>0$ a real coherent amplitude. Set $\Pi_r=\sum_{n\equiv r\;({\rm mod}\;2(S+1))}|n\rangle\langle n|$, $N_a^r=\langle a|\Pi_r|a\rangle$, and $|\mu_a\rangle=\Pi_{(S+1)\mu}|a\rangle/\sqrt{N_a^{(S+1)\mu}}$ for $\mu=0,1$. All $N_a^r$ are positive, these two states are normalized and orthogonal, and
--
--   $$N_a^{(S+1)\mu}=\frac1{2(S+1)}\sum_{s=0}^{2S+1}(-1)^{\mu s}\exp\!\left[a^2\left(e^{i\pi s/(S+1)}-1\right)\right],\qquad \hat a^{2(S+1)}|\mu_a\rangle=a^{2(S+1)}|\mu_a\rangle.$$
--
--   The states belong to the natural domain of the annihilation power. For $0<\gamma<1$, the loss Kraus operator $E_\ell$ and $C=e^{2\pi i\hat n/(S+1)}$ satisfy $CE_\ell|\mu_a\rangle=e^{-2\pi i\ell/(S+1)}E_\ell|\mu_a\rangle$ for $0\le\ell\le S$. These $S+1$ phases are distinct. Its specified square root $e^{i\pi\hat n/(S+1)}$ acts on the two logical states with eigenvalues $(-1)^\mu$. Thus the check distinguishes these loss counts, with residues repeating thereafter.
-- source:
--   Performance and structure of single-mode bosonic codes, arXiv:1708.05010v3, PDF p. 9, §V (5.5)–(5.7): cat normalization, eigenoperator and loss syndromes

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P65

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P65

open MeasureTheory Filter

open QAlgorithms.Papers.Independent.Frontier18.P14 (displacementEntry)

open QAlgorithms.Papers.Independent.Dependency50.P40 (outputFirstChoi)

open scoped ComplexConjugate Matrix Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.9 (5.5)--(5.7): normalization, annihilation eigenoperator, and the
S+1 distinct loss syndromes, with normalized physical states on the full domain.
The printed claim of non-unit-modulus check eigenvalues is a source slip and is omitted. -/
theorem cat_checks (a : ℝ) (ha : 0 < a) (S : ℕ) (g : ℝ) (hg0 : 0 < g) (hg1 : g < 1) :
    (∀ r : ℤ, 0 < catNorm a S r) ∧
    (∀ mu : Fin 2, (catNorm a S ((S + 1) * mu.val : ℕ) : ℂ) = catNormFourier a S mu) ∧
    (∀ mu : Fin 2, fockDomain (catCodeCoordinates a S mu) ∧ fockNormSq (catCodeCoordinates a S mu) = 1 ∧
      annDomain (2 * (S + 1)) (catCodeCoordinates a S mu) ∧
      annPower (2 * (S + 1)) (catCodeCoordinates a S mu) = (a : ℂ) ^ (2 * (S + 1)) • catCodeCoordinates a S mu) ∧
    fockInner (catCodeCoordinates a S 0) (catCodeCoordinates a S 1) = 0 ∧
    (∀ mu : Fin 2, residueLogicalZ S (catCodeCoordinates a S mu) = (-1 : ℂ) ^ mu.val • catCodeCoordinates a S mu) ∧
    (∀ (l : Fin (S + 1)) (mu : Fin 2),
      residueCheck S (lossVector g l.val (catCodeCoordinates a S mu)) =
        Complex.exp (-Complex.I * (2 * Real.pi * (l.val : ℝ) / (S + 1))) •
          lossVector g l.val (catCodeCoordinates a S mu)) ∧
    Function.Injective (fun l : Fin (S + 1) =>
      Complex.exp (-Complex.I * (2 * Real.pi * (l.val : ℝ) / (S + 1)))) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P65

end
