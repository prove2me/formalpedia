-- Prove2me | Theorems.Thm_StableCountSub3_lemma_5_8
-- name    : StableCountSub3.lemma_5_8
-- status  : Open
-- author  : @CGTMoyano
-- created : 2026-11-24T17:53:17.176566+00:00
-- url     : https://prove2.me/theorems/28978664-a0df-4b85-bcad-08cac7072bbb
-- title:
--   Lemma 5.8 — sum of basic credits: $\sum_m g^\pm_{\rm basic}(D,m)=n\delta_1-(\delta_1-\delta_2)(|B|+|C|)$
-- statement:
--   Fix an instance $I$ of the stable marriage problem with $n$ men and $n$ women, a downset $D$ of the rotation poset $(\mathcal R,\preceq)$ (the reference stable matching $\mu_D$), and an outward direction $\pm$ (forward: the order $P^+(D)$ on $\mathcal R\setminus D$; backward: the reverse order $P^-(D)$ on $D$). For a man $m$ write $K_m(k)$, $S_m(k)$ and $s_m(k)$ for his $k$-th principal cone, its support (the set of men participating in its rotations) and the support size ($\infty$ when the $k$-th rotation of $m$ in the outward order does not exist). A man is *simple* if $s_m(1)=2$; $C=\{m : s_m(1)=2,\ s_m(2)=3\}$ and $B=\{m : s_m(1)=2,\ s_m(2)\ge 4\}$ (Definition 5.2). Executing a rotation means eliminating it (forward) or undoing its elimination (backward); a *swap* $(a,b)$ is a rotation whose execution exchanges the partners of the two men $a\ne b$. Let $I=\phi(C)$ be the set of images (Definition 5.4), and let the basic credit $g^\pm_{\rm basic}(D,m)$ be $0$ for $m\in C$, $\delta_2$ for $m\in B$, $\delta_1+\delta_2$ for $m\in I$ and $\delta_1$ for every other man (Definition 5.7, Table 1), where
--   $$\delta_d=\sum_{j\ge d}\frac{2\log\frac{j+1}{j}}{(j+1)(j+2)(j+3)}.$$
--
--   **Lemma 5.8.** For the fixed downset $D$ and direction,
--   $$\sum_{m\in M} g^\pm_{\rm basic}(D,m)=n\,\delta_1-(\delta_1-\delta_2)\,(|B|+|C|).$$
--
--   The identity reduces the dependence of the total basic credit on the classes to the number $|B|+|C|$ of simple men; averaged over pointed matchings it yields Lemma 5.14.
--
--   **Formalization Note** The basic credit is `basicCredit I D m dir`, defined by the case distinction $C$, then $B$, then $I$, then the rest; $|B|$ and $|C|$ are cardinalities of filters of `Finset.univ`, cast to $\mathbb R$.
-- source:
--   Kawarabayashi, Wada, Yoneda 2026, A Sub-3^n Upper Bound on the Number of Stable Matchings, arXiv:2611.06604v1, Lemma 5.8, p. 29 (Section 5.3), with Definition 5.7 and Table 1

import Mathlib
import Definitions.Def_StableCountSub3_Credits

open StableMatching

namespace StableCountSub3

open Classical in
/-- Lemma 5.8: for a fixed downset and direction,
`∑_{m ∈ M} g^±_basic(D, m) = n δ₁ − (δ₁ − δ₂)(|B| + |C|)`. -/
theorem lemma_5_8 {n : ℕ} (I : Instance n) (D : Finset (Rot n)) (hD : IsDownset I D)
    (dir : Dir) :
    ∑ m : Fin n, basicCredit I D m dir =
      n * delta 1 - (delta 1 - delta 2) *
        (((Finset.univ.filter fun m => InB I D m dir).card : ℝ) +
          ((Finset.univ.filter fun m => InC I D m dir).card : ℝ)) := by sorry

end StableCountSub3
