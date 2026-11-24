-- Prove2me | Theorems.Thm_StableCountSub3_lemma_5_5
-- name    : StableCountSub3.lemma_5_5
-- status  : Open
-- author  : @CGTMoyano
-- created : 2026-11-24T17:53:18.859568+00:00
-- url     : https://prove2.me/theorems/1bfcea6c-22d3-4d31-bba0-572e773846ec
-- title:
--   Lemma 5.5 — the image map $\phi$: $K_{\phi(m)}(1)=K_m(2)$, $\phi$ injective, $s_{\phi(m)}(1)=3$, $s_{\phi(m)}(2)\ge4$
-- statement:
--   Fix an instance $I$ of the stable marriage problem with $n$ men and $n$ women, a downset $D$ of the rotation poset $(\mathcal R,\preceq)$ (the reference stable matching $\mu_D$), and an outward direction $\pm$ (forward: the order $P^+(D)$ on $\mathcal R\setminus D$; backward: the reverse order $P^-(D)$ on $D$). For a man $m$ write $K_m(k)$, $S_m(k)$ and $s_m(k)$ for his $k$-th principal cone, its support (the set of men participating in its rotations) and the support size ($\infty$ when the $k$-th rotation of $m$ in the outward order does not exist). A man is *simple* if $s_m(1)=2$; $C=\{m : s_m(1)=2,\ s_m(2)=3\}$ and $B=\{m : s_m(1)=2,\ s_m(2)\ge 4\}$ (Definition 5.2). Executing a rotation means eliminating it (forward) or undoing its elimination (backward); a *swap* $(a,b)$ is a rotation whose execution exchanges the partners of the two men $a\ne b$. For $m\in C$, Lemma 5.3 gives $K_m(2)=\{\tau,\sigma\}$ with $\sigma=(m,a)$ the second rotation of $m$; the man $a$ is the *image* $\phi(m)$ of $m$ (Definition 5.4).
--
--   **Lemma 5.5.** Let $m\in C$ and $a=\phi(m)$. Then
--
--   1. $K_a(1)=K_m(2)$;
--   2. the map $\phi : C\to M$ is injective;
--   3. $s_a(1)=3$ and $s_a(2)\ge 4$ (including $s_a(2)=\infty$).
--
--   Consequently $|\phi(C)|=|C|$ and no image is simple, so the class $I=\phi(C)$ is disjoint from $B\cup C$. These facts drive the basic-credit count (Lemma 5.8) and the averaging bounds of Lemmas 5.13 and 5.14.
--
--   **Formalization Note** $\phi(m)$ is `image I D m dir`, $K_x(k)$ is `principalCone I D x dir k` (an `Option`), and $s_x(k)$ is `ssize I D x dir k : ℕ∞` with $\infty = \top$. Injectivity is stated on $C$, where $\phi$ is defined.
-- source:
--   Kawarabayashi, Wada, Yoneda 2026, A Sub-3^n Upper Bound on the Number of Stable Matchings, arXiv:2611.06604v1, Lemma 5.5, p. 28 (Section 5.2), with Definition 5.4 and the remark after the proof

import Mathlib
import Definitions.Def_StableCountSub3_Credits

open StableMatching

namespace StableCountSub3

/-- Lemma 5.5: for `m ∈ C` and `a = φ(m)`: `K_a(1) = K_m(2)`, `s_a(1) = 3`, `s_a(2) ≥ 4`;
and the map `φ` is injective on `C`. -/
theorem lemma_5_5 {n : ℕ} (I : Instance n) (D : Finset (Rot n)) (hD : IsDownset I D)
    (dir : Dir) :
    (∀ m, InC I D m dir →
      principalCone I D (image I D m dir) dir 1 = principalCone I D m dir 2 ∧
      ssize I D (image I D m dir) dir 1 = 3 ∧ 4 ≤ ssize I D (image I D m dir) dir 2) ∧
    (∀ m m', InC I D m dir → InC I D m' dir → image I D m dir = image I D m' dir → m = m') := by
  sorry

end StableCountSub3
