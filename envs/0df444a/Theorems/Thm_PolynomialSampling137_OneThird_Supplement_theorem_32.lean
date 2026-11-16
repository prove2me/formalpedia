-- Prove2me | Theorems.Thm_PolynomialSampling137_OneThird_Supplement_theorem_32
-- name    : PolynomialSampling137.OneThird.Supplement.theorem_32
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:57:18.917113+00:00
-- url     : https://prove2.me/theorems/6620dce1-d43d-4434-8c6d-d2355d038f40
-- title:
--   Theorem 32 — Shifted-inverse overlap (56), including appended parameter and unrestricted appended competing map
-- statement:
--   Fix $K=\mathbb F_{2^r}$, $r\ge1$, $q=2^r$, any binary basis, and $S\subset K$ with $1\le L=|S|<q$. Let $D_{K,S}$ be the law of $((X+a)^{-1})_{a\in S}$ for uniform $X\in K$, with inverse at zero equal to zero. For any $d\ge0$ with $L\ge2^d$, any finite $s$, and any $Q:\mathbb F_2^s\to K^S$ whose binary coordinates have degree at most $d$, put $M=2^{d+1}$ and $\kappa_d=M-d-1$. Then
--   $$\operatorname{Ov}(P_Q,D_{K,S})\le\min\{1,L/q+((M-1)/q)^{1/\kappa_d}\}.$$
--   The same bound holds when the target appends $X$ and the competing sampler appends any map $R:\mathbb F_2^s\to K$, without a degree condition on $R$. Sampler outputs need not lie in the target support. This companion theorem uses the same collision criterion as the odd-power construction, with the additive exceptional-point mass outside the root.
--
--   Differences from the source:
--   - encoding: finite binary vector spaces and probability laws → Fin-indexed words, finite fiber sums and structural predicates; reason: the representations preserve all source instances, including zero dimensions and zero masses
-- source:
--   Yan Zhong, Exponential Sampling Lower Bounds for Polynomial Sources, STOC 2027 submission #137 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/137.pdf, Theorem 32, printed p. 41; PDF p. 43

import Definitions.Def_PolynomialSampling137_OneThird_Supplement_BinaryFields

noncomputable section

namespace PolynomialSampling137.OneThird.Supplement

theorem theorem_32 (r : ℕ) (K : BinaryField r)
    [DecidableEq K.Carrier] (S : Finset K.Carrier) (hS : 1 ≤ S.card)
    (hSq : S.card < 2 ^ r) (d : ℕ) (hL : 2 ^ d ≤ S.card)
    (s : ℕ) (Q : Word s → S → K.Carrier)
    (hQ : ∀ a i, DegreeLE d (fun x => K.coords (Q x a) i)) :
    overlap (UniformImage Q) (ShiftedInverseLaw K S) ≤
      min 1 ((S.card : ℝ) / (2 : ℝ) ^ r +
        ((((2 : ℝ) ^ (d + 1) - 1) / (2 : ℝ) ^ r) ^
          (1 / (CollisionExponent d : ℝ)))) ∧
    (∀ R : Word s → K.Carrier,
      overlap (UniformImage (fun x => (Q x, R x))) (AppendedInverseLaw K S) ≤
        min 1 ((S.card : ℝ) / (2 : ℝ) ^ r +
          ((((2 : ℝ) ^ (d + 1) - 1) / (2 : ℝ) ^ r) ^
            (1 / (CollisionExponent d : ℝ))))) := by sorry

end PolynomialSampling137.OneThird.Supplement
