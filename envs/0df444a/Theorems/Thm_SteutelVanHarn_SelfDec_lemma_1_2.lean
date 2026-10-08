-- Prove2me | Theorems.Thm_SteutelVanHarn_SelfDec_lemma_1_2
-- name    : SteutelVanHarn.SelfDec.lemma_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:50:02.19707+00:00
-- url     : https://prove2.me/theorems/f65b4235-ed8e-4aa7-8279-273ebeac818e
-- title:
--   Lemma 1.2 — for $0<p_0<1$: inf div ⟺ (1.3) ⟺ (1.4) ⟺ $r_n\ge0$ in (1.5)
-- statement:
--   Let $(p_n)$ be a distribution on $\mathbb N_0$ with p.g.f. $P$ and $0<p_0<1$, and let $(r_n)$ be its canonical sequence, defined by
--   $$
--   (n+1)\,p_{n+1}=\sum_{k=0}^{n}p_k\,r_{n-k}\qquad(n\in\mathbb N_0).\tag{1.5}
--   $$
--   Then:
--
--   1. $P$ is infinitely divisible iff $P(z)=\exp\{\lambda(G(z)-1)\}$ (form (1.3)) for some $\lambda>0$ and some p.g.f. $G$ of a distribution $(g_n)$ on $\mathbb N_0$ with $g_0=0$;
--   2. the pair $(\lambda,(g_n))$ in (1.3) is unique;
--   3. $P$ is infinitely divisible iff
--   $$
--   P(z)=\exp\Big\{-\int_z^1R(u)\,du\Big\},\qquad R(u)=\sum_{n\ge0}r_nu^n,\tag{1.4}
--   $$
--   for some sequence $r_n\ge0$ (form (1.4));
--   4. whenever (1.4) holds with $r_n\ge0$, necessarily $\sum_{n\ge0}r_n(n+1)^{-1}<\infty$, and $(r_n)$ is the canonical sequence, i.e. the $p_n$ satisfy (1.5) with these $r_n$;
--   5. $P$ is infinitely divisible iff its canonical sequence satisfies $r_n\ge0$ for all $n$.
--
--   This is the classical characterization of infinitely divisible distributions on $\mathbb N_0$ as compound Poisson distributions; the paper quotes it from Feller and Steutel and uses it twice in the proof of Theorem 2.2.
--
--   **Formalization Note** (1.3) is required on $[0,1]$ and (1.4) on $[0,1)$. Form (1.4) includes the convergence of $R$ on $[0,1)$ and the finiteness of $\int_z^1R$, which the paper's formula presupposes. The "i.e." of the paper (the $r_n$ of (1.4) are those of (1.5)) is item 4.
-- source:
--   Steutel & van Harn, Discrete analogues of self-decomposability and stability, Memorandum COSOR 78-07, TH Eindhoven (1978), p. 2, Lemma 1.2, (1.3), (1.4), (1.5)

import Definitions.Def_SteutelVanHarn_SelfDec_InfDiv

namespace SteutelVanHarn.SelfDec

theorem lemma_1_2 (p : ℕ → ℝ) (hp : IsDistribution p) (hp0 : 0 < p 0) (hp1 : p 0 < 1) :
    (IsInfDiv p ↔ ∃ (lam : ℝ) (g : ℕ → ℝ), HasForm13 p lam g) ∧
    (∀ (lam₁ lam₂ : ℝ) (g₁ g₂ : ℕ → ℝ),
      HasForm13 p lam₁ g₁ → HasForm13 p lam₂ g₂ → lam₁ = lam₂ ∧ g₁ = g₂) ∧
    (IsInfDiv p ↔ ∃ r : ℕ → ℝ, HasForm14 p r) ∧
    (∀ r : ℕ → ℝ, HasForm14 p r →
      Summable (fun n : ℕ => r n / ((n : ℝ) + 1)) ∧ r = canonicalSeq p) ∧
    (IsInfDiv p ↔ ∀ n, 0 ≤ canonicalSeq p n) := by sorry

end SteutelVanHarn.SelfDec
