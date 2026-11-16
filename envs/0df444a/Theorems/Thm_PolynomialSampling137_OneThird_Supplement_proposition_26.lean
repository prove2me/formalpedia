-- Prove2me | Theorems.Thm_PolynomialSampling137_OneThird_Supplement_proposition_26
-- name    : PolynomialSampling137.OneThird.Supplement.proposition_26
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:53:08.750881+00:00
-- url     : https://prove2.me/theorems/e90c729d-0078-4ec3-a201-26e5894ee45c
-- title:
--   Proposition 26 — Finite flat-sampling Fourier/counting bound (40), valid for arbitrary seed lengths
-- statement:
--   Let $T\subseteq\mathbb F_2^n$ have size $q=2^k$, with $1\le k\le n$, and let $\pi$ be its uniform, $\varepsilon$-biased law. For every map $F$ of Eq. (36), every finite seed length, and every $t\ge0$, put $u=\lfloor t/2\rfloor$. Then
--   $$\operatorname{Ov}(P_F,\pi)\le\min\{1,4\,9^t\max\{\varepsilon,q\,2^{M-n}/V(M,u)\}\}.$$
--   Here $V(M,u)=\sum_{j=0}^{\min(u,M)}\binom Mj$. The estimate includes $M=0$, $t=0$ and $u>M$. Shared gates use a single vector label; the seed length is arbitrary. This finite counting bound supports the inverse-line circuit target.
--
--   Differences from the source:
--   - encoding: finite binary vector spaces and probability laws → Fin-indexed words, finite fiber sums and structural predicates; reason: the representations preserve all source instances, including zero dimensions and zero masses
--   - generalization: M counts the simplified nonlinear flat terms → M may also count redundant, empty, whole-space or codimension-one flat terms; reason: the normalized source representation is included; the Fourier and counting estimate remains valid for unsimplified flat lists
-- source:
--   Yan Zhong, Exponential Sampling Lower Bounds for Polynomial Sources, STOC 2027 submission #137 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/137.pdf, Proposition 26, printed p. 32; PDF p. 34

import Definitions.Def_PolynomialSampling137_OneThird_Supplement_BinaryFields
import Definitions.Def_PolynomialSampling137_OneThird_Supplement_Circuits

noncomputable section

namespace PolynomialSampling137.OneThird.Supplement

theorem proposition_26 {n s : ℕ} (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n)
    (T : Finset (Word n)) (hT : T.card = 2 ^ k) (ε : ℝ)
    (hε : SmallBias (UniformOn T) ε) (M t : ℕ)
    (A : Word s →ᵃ[ZMod 2] Word n) (v : Fin M → Word n)
    (B : Fin M → AffineSubspace (ZMod 2) (Word s)) :
    overlap (samplerMass (FlatMap M A v B)) (UniformOn T) ≤
      min 1 (4 * (9 : ℝ) ^ t * max ε
        ((2 : ℝ) ^ k * (2 : ℝ) ^ ((M : ℤ) - n) / HammingVolume M (t / 2))) := by sorry

end PolynomialSampling137.OneThird.Supplement
