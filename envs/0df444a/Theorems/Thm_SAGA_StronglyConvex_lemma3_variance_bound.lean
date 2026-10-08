-- Prove2me | Theorems.Thm_SAGA_StronglyConvex_lemma3_variance_bound
-- name    : SAGA.StronglyConvex.lemma3_variance_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T13:11:05.197684+00:00
-- url     : https://prove2.me/theorems/18f1ede5-7f88-4c61-893c-8f8e281c7ab1
-- title:
--   Lemma 3 (= Lemma 7), sign of $\gamma f'(x^*)$ corrected as in its proof — variance bound for the SAGA step
-- statement:
--   Let $n\ge1$, let $f_1',\dots,f_n':\mathbb R^d\to\mathbb R^d$ be arbitrary maps and $f'=\frac1n\sum_i f_i'$. Fix a step $\gamma\in\mathbb R$, points $\phi_1,\dots,\phi_n$, $x^*$, $x$ in $\mathbb R^d$ and $\beta>0$. For each index $j$ let $w_j=x-\gamma\big[f_j'(x)-f_j'(\phi_j)+\frac1n\sum_i f_i'(\phi_i)\big]$ be the SAGA gradient step of eq. (1), and let $\mathbb E$ denote the average over $j$ uniform in $\{1,\dots,n\}$. Then
--
--   $$
--   \mathbb E\big\|w_j-x+\gamma f'(x^*)\big\|^2\;\le\;\gamma^2(1+\beta^{-1})\,\mathbb E\|f_j'(\phi_j)-f_j'(x^*)\|^2+\gamma^2(1+\beta)\,\mathbb E\|f_j'(x)-f_j'(x^*)\|^2-\gamma^2\beta\,\|f'(x)-f'(x^*)\|^2 .
--   $$
--
--   This bounds the second moment of the SAGA gradient estimator around the gradient at the optimum, and is applied in the proof of Theorem 1 with $x=x^k$, $\phi=\phi^k$.
--
--   **Formalization Note** The paper prints $\mathbb E\|w^{k+1}-x^k-\gamma f'(x^*)\|^2$ on the left. The first line of the proof of Lemma 7 (p. 11) and the use of the lemma in the proof of Theorem 1 (p. 7) both have $+\gamma f'(x^*)$, and the printed version is false whenever $f'(x^*)\ne0$ (take $\phi_i=x=x^*$: the left side is $4\gamma^2\|f'(x^*)\|^2$ and the right side is $0$). The corrected sign is formalized. The statement is pure algebra: no convexity, smoothness or gradient relation is needed. The average over $j$ is written as $\frac1n\sum_{j}$ over `Fin n`.
-- source:
--   Defazio, Bach & Lacoste-Julien, SAGA, arXiv:1407.0202v3, p. 7, Lemma 3 (restated as Lemma 7 with proof, p. 11); sign corrected per the proof, p. 11, and its use in Theorem 1, p. 7

import Mathlib
import Definitions.Def_SAGA_StronglyConvex_sagaW

namespace SAGA.StronglyConvex

/-- Lemma 3 (p. 7, = Lemma 7, p. 11), **with the sign of `γ f'(x*)` corrected** to `+`, as in the
first line of the proof of Lemma 7 (p. 11) and in its use in Theorem 1 (p. 7). The printed
`w^{k+1} - x^k - γ f'(x*)` makes the lemma false whenever `f'(x*) ≠ 0` (take `φ_i = x^k = x*`).
`E` is the average over the uniformly drawn index `j`; `f' = (1/n) Σ_i f'_i`. Pure algebra:
the maps `f'_i` and the step `γ` are arbitrary. -/
theorem lemma3_variance_bound {d n : ℕ} (hn : 0 < n)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (γ β : ℝ) (hβ : 0 < β)
    (φ : Fin n → EuclideanSpace ℝ (Fin d)) (xs x : EuclideanSpace ℝ (Fin d)) :
    (1 / (n : ℝ)) * ∑ j, ‖sagaW f' γ x φ j - x + γ • ((1 / (n : ℝ)) • ∑ i, f' i xs)‖ ^ 2 ≤
      γ ^ 2 * (1 + β⁻¹) * ((1 / (n : ℝ)) * ∑ j, ‖f' j (φ j) - f' j xs‖ ^ 2)
        + γ ^ 2 * (1 + β) * ((1 / (n : ℝ)) * ∑ j, ‖f' j x - f' j xs‖ ^ 2)
        - γ ^ 2 * β * ‖(1 / (n : ℝ)) • ∑ i, f' i x - (1 / (n : ℝ)) • ∑ i, f' i xs‖ ^ 2 := by sorry

end SAGA.StronglyConvex
