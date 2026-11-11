-- Prove2me | Theorems.Thm_TensorBeyond_Main_lemma_5_3
-- name    : TensorBeyond.Main.lemma_5_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:15:03.405368+00:00
-- url     : https://prove2.me/theorems/da1bb1a6-b6ef-4cdf-97bd-c356f37347dd
-- title:
--   Lemma 5.3 ([GM15]) — high $(d+2)$-th and bounded $d$-th pseudo-moments give $\tilde{\mathbb E}\langle v_i,x\rangle^r\ge e^{-\Omega(\varepsilon r)}$ for some $i$
-- statement:
--   Let $v_1,\dots,v_m\in\{\pm1\}^n$ be arbitrary, $T=\sum_iv_i^{\otimes4}$, $\langle x,y\rangle=\frac1nx^\top y$ and $\mu=(3n^2-2n)/n^4$. For every $a>0$ and every even $d$ there are $A,B,c_0>0$ and $N_0$ such that for all $n\ge N_0$, $n\le m\le n^a$, every $\varepsilon>0$, every even $r\ge A\log n/\varepsilon$, every slack $\delta\in\mathbb R$ and every pseudo-expectation $\tilde{\mathbb E}$ of degree $Br$ satisfying (2.4), i.e. $\langle T,x^{\otimes4}\rangle\ge1+m\mu-\delta$ and $x_u^2=1$: if
--   $$\tilde{\mathbb E}\Big[\sum_i\langle v_i,x\rangle^{d+2}\Big]\ge1-\varepsilon\quad\text{and}\quad\tilde{\mathbb E}\Big[\sum_i\langle v_i,x\rangle^{d}\Big]\le1+\varepsilon,$$
--   then there is $i\in[m]$ with $\tilde{\mathbb E}[\langle v_i,x\rangle^r]\ge\exp(-c_0\varepsilon r)$.
--
--   This is the moment condition under which the rounding of Barak, Kelner and Steurer recovers a component; Lemmas 6.3 and 7.16 verify its premise for $k=4$ and $k=3$. As printed it holds for every $\varepsilon>0$; it is stated so here, although it fails for large $\varepsilon$ (a finding recorded separately).
--
--   Differences from the source:
--   - reading: r = O(log n/ε) → every even r ≥ A·log n/ε; reason: obvious typo, the proof's last step uses r = Ω(log n/ε) as Lemma 5.2 does, and with an upper bound only the claim fails already at r = 2
--   - reading: pseudo-expectation of degree O(r), exp(−Ω(εr)) → degree B·r, exp(−c₀ε r), with A, B, c₀, N₀ depending only on a and d; reason: the paper's O/Ω with constants fixed before n, m, r, ε
--   - generalization: constraints (2.4) with slack o(1) → slack δ arbitrary; reason: every o(1) slack is one value of δ
--   - reading: (2.4) for general k with μ = E⟨v_i, v_j⟩⁴ → k = 4, μ = (3n² − 2n)/n⁴; reason: μ is the k = 4 quantity of §2.2 and (6.1); with δ arbitrary the constraint excludes no pseudo-expectation the k = 3 use needs
--   - reading: standing assumption n ≤ m ≤ poly(n) of §4.1 → n ≤ m ≤ n^a for an arbitrary a > 0; reason: the proof uses that m and n are polynomially related
-- source:
--   Jha, Mazzali, Xu, Tensor Decomposition Beyond the Spectral Threshold, STOC 2027 submission (held manuscript, sha256 988d801c…), pp. 30–31 (PDF 32–33), Lemma 5.3 ([GM15]); (2.4) on p. 6 (PDF 8)

import Mathlib
import Definitions.Def_TensorBeyond_Main_Model
import Definitions.Def_TensorBeyond_Main_SoS
import Definitions.Def_TensorBeyond_Main_Polys

set_option autoImplicit false

namespace TensorBeyond.Main

/-- Lemma 5.3 ([GM15]), with `r = Ω(log n/ε)`: for every `a > 0` and every even `d` there are
`A, B, c₀ > 0` and `N₀` such that for all `n ≥ N₀`, `n ≤ m ≤ n^a`, every sample, every `ε > 0`,
every even `r ≥ A log n/ε` and every pseudo-expectation `Ẽ` of degree `B r` satisfying (2.4)
(`⟨T, x^{⊗4}⟩ ≥ 1 + mμ − δ`, `x_u² = 1`, any slack `δ`): if `Ẽ[∑_i ⟨v_i,x⟩^{d+2}] ≥ 1 − ε` and
`Ẽ[∑_i ⟨v_i,x⟩^d] ≤ 1 + ε`, then `Ẽ[⟨v_i, x⟩^r] ≥ exp(−c₀ ε r)` for some `i`. -/
theorem lemma_5_3 (a : ℝ) (ha : 0 < a) (d : ℕ) (hd : Even d) :
    ∃ A B c₀ : ℝ, 0 < A ∧ 0 < B ∧ 0 < c₀ ∧ ∃ N₀ : ℕ,
      ∀ n m : ℕ, N₀ ≤ n → n ≤ m → (m : ℝ) ≤ (n : ℝ) ^ a →
        ∀ (v : Sample n m) (ε : ℝ), 0 < ε →
        ∀ r : ℕ, Even r → A * Real.log (n : ℝ) / ε ≤ (r : ℝ) →
        ∀ (δ : ℝ) (E : Poly n →ₗ[ℝ] ℝ),
          IsPseudoExp (B * (r : ℝ)) (progP 4 v (xi4 n m δ)) E →
          1 - ε ≤ E (R v (d + 2)) → E (R v d) ≤ 1 + ε →
          ∃ i : Fin m, Real.exp (-(c₀ * ε * (r : ℝ))) ≤ E (ipPoly (vec v i) ^ r) := by sorry

end TensorBeyond.Main
