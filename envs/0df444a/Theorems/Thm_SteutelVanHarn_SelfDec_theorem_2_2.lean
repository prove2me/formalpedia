-- Prove2me | Theorems.Thm_SteutelVanHarn_SelfDec_theorem_2_2
-- name    : SteutelVanHarn.SelfDec.theorem_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:51:28.459905+00:00
-- url     : https://prove2.me/theorems/22de5afe-7975-48ce-853e-17e1437e6920
-- title:
--   Theorem 2.2 — $P$ is discrete self-dec ⟺ $P(z)=\exp\{-\lambda\int_z^1\frac{1-G(u)}{1-u}du\}$ ⟺ $P$ is inf div with nonincreasing $r_n$
-- statement:
--   Let $(p_n)$ be a distribution on $\mathbb N_0$ with p.g.f. $P$ and $0<p_0<1$ (the standing assumption of §2). Then:
--
--   1. $(p_n)$ is discrete self-decomposable if and only if $P$ has the form
--   $$
--   P(z)=\exp\Big\{-\lambda\int_z^1\frac{1-G(u)}{1-u}\,du\Big\}\qquad(0\le z<1),\tag{2.4}
--   $$
--   where $\lambda>0$ and $G$ is the p.g.f. of a distribution $(g_n)$ on $\mathbb N_0$ with $G(0)=g_0=0$;
--   2. the pair $(\lambda,(g_n))$ in (2.4) is unique;
--   3. equivalently, $(p_n)$ is discrete self-decomposable if and only if it is infinitely divisible and its canonical sequence $(r_n)$, defined by $(n+1)p_{n+1}=\sum_{k=0}^np_kr_{n-k}$, is nonincreasing.
--
--   Here discrete self-decomposability means: for every $\alpha\in(0,1)$, $P(z)=P(1-\alpha+\alpha z)P_\alpha(z)$ with $P_\alpha$ a p.g.f. (Definition 2.1). The theorem is the discrete counterpart of the Lévy–Khintchine-type canonical form of self-decomposable laws on the real line, with binomial thinning replacing scalar multiplication.
--
--   **Formalization Note** (2.4) includes, for each $z\in[0,1)$, the finiteness of the improper integral (integrability of $(1-G(u))/(1-u)$ on $(z,1)$), because Lean's integral of a non-integrable function is $0$. The standing assumption $0<p_0<1$ excludes the point mass at $0$, which is self-decomposable but has no representation (2.4) with $\lambda>0$.
-- source:
--   Steutel & van Harn, Discrete analogues of self-decomposability and stability, Memorandum COSOR 78-07, TH Eindhoven (1978), p. 2 (standing assumption 0 < p₀ < 1, §2), p. 3, Theorem 2.2, (2.4)

import Definitions.Def_SteutelVanHarn_SelfDec_SelfDec

namespace SteutelVanHarn.SelfDec

theorem theorem_2_2 (p : ℕ → ℝ) (hp : IsDistribution p) (hp0 : 0 < p 0) (hp1 : p 0 < 1) :
    (IsDiscreteSelfDec p ↔ ∃ (lam : ℝ) (g : ℕ → ℝ), HasForm24 p lam g) ∧
    (∀ (lam₁ lam₂ : ℝ) (g₁ g₂ : ℕ → ℝ),
      HasForm24 p lam₁ g₁ → HasForm24 p lam₂ g₂ → lam₁ = lam₂ ∧ g₁ = g₂) ∧
    (IsDiscreteSelfDec p ↔ IsInfDiv p ∧ Antitone (canonicalSeq p)) := by sorry

end SteutelVanHarn.SelfDec
