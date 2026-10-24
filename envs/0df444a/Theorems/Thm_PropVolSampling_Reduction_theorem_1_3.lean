-- Prove2me | Theorems.Thm_PropVolSampling_Reduction_theorem_1_3
-- name    : PropVolSampling.Reduction.theorem_1_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:48:39.105362+00:00
-- url     : https://prove2.me/theorems/1afcb951-49a1-4394-a884-b2d6afd1b6fe
-- title:
--   Theorem 1.3, p. 3 — proportional volume sampling with an α-approximate (d−1, d)-wise independent measure is an α-approximation for A-optimal design
-- statement:
--   Let $1\le d\le k\le n$ be integers and $V=[v_1,\dots,v_n]$ a real $d\times n$ matrix. The A-optimal design problem asks for $S\subseteq[n]$, $|S|=k$, minimising $\operatorname{tr}(V_SV_S^\top)^{-1}=\operatorname{tr}(\sum_{i\in S}v_iv_i^\top)^{-1}$; let $\mathrm{OPT}$ be its optimal value.
--
--   Let $x$ be an optimal solution of the convex relaxation (1)–(3),
--   $$\min\ \operatorname{tr}\Big(\sum_{i=1}^nx_iv_iv_i^\top\Big)^{-1}\quad\text{s.t.}\quad\sum_ix_i=k,\ 0\le x_i\le1,$$
--   with finite value $\mathrm{CP}$, and let $\mu$ be a probability measure on $\mathcal U_k$ or $\mathcal U_{\le k}$ that is $\alpha$-approximate $(d-1,d)$-wise independent with respect to $x$. Run Algorithm 1: sample $\mathcal S$ by proportional volume sampling, $\Pr[\mathcal S=S]\propto\mu(S)\det(V_SV_S^\top)$, and output $\mathcal S$ padded by arbitrary further indices to a set $\operatorname{pad}(\mathcal S)\supseteq\mathcal S$ of size $k$. Then
--
--   1. the algorithm is an $\alpha$-approximation in expectation: for every $k$-set $S^{\mathrm{opt}}$,
--   $$\mathbb E\Big[\operatorname{tr}\big(V_{\operatorname{pad}(\mathcal S)}V_{\operatorname{pad}(\mathcal S)}^\top\big)^{-1}\Big]\le\alpha\,\operatorname{tr}\big(V_{S^{\mathrm{opt}}}V_{S^{\mathrm{opt}}}^\top\big)^{-1},$$
--   hence the expected objective is at most $\alpha\,\mathrm{OPT}$;
--   2. the integrality gap of the relaxation is at most $\alpha$: some $k$-set $S$ has $\operatorname{tr}(V_SV_S^\top)^{-1}\le\alpha\,\mathrm{CP}$.
--
--   This reduces approximating A-optimal design to constructing approximately independent distributions; the paper's Theorems 1.4 and 1.5 instantiate it with hard-core distributions.
--
--   **Formalization Note** The page assumes such a $\mu$ for every feasible $x$; as the remark after Theorem 1.3 says, only the optimal $x$ is used, so the Lean statement takes one optimal $x$ and one $\mu$, which implies the page's form. Approximate independence is cross-multiplied (Definition 1.2 wherever its ratio is defined). The following are added: the normaliser $\sum_S\mu(S)\det(V_SV_S^\top)$ is positive (Definition 1.1 presupposes it; otherwise $\mu'$ is undefined); $\sum_ix_iv_iv_i^\top$ is positive definite (part of optimality with finite $\mathrm{CP}$); $1\le d$ (for $d-1$). $\mathrm{OPT}$ is expressed by quantifying over $k$-sets with positive definite Gram matrix, because Lean's inverse is a junk $0$ on singular matrices; those sets have value $+\infty$ on the page. The padding is an arbitrary map $\operatorname{pad}$ with $S\subseteq\operatorname{pad}(S)$ and $|\operatorname{pad}(S)|=k$ on the support of $\mu$ (for $\mu$ on $\mathcal U_k$, take $\operatorname{pad}=\mathrm{id}$).
-- source:
--   Nikolov, Singh, Tantipongpipat, Proportional Volume Sampling and Approximation Algorithms for A-Optimal Design, arXiv:1802.08318v5, p. 3, Theorem 1.3 and the remark after it (proof §2, pp. 7–10; Algorithm 1, p. 8)

import Mathlib
import Definitions.Def_PropVolSampling_Reduction_Model

namespace PropVolSampling.Reduction
open Matrix Finset

theorem theorem_1_3 {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ) (k : ℕ) (hd : 1 ≤ d) (hdk : d ≤ k)
    (hkn : k ≤ n) (x : Fin n → ℝ) (hx : IsRelaxOptimal V k x)
    (μ : Finset (Fin n) → ℝ) (hμ : IsSetDist k μ) (α : ℝ) (hα : IsApproxIndep d α x μ)
    (hZ : 0 < pvsNormalizer V μ) (pad : Finset (Fin n) → Finset (Fin n))
    (hpad : ∀ S, μ S ≠ 0 → S ⊆ pad S ∧ (pad S).card = k) :
    (∀ Sopt : Finset (Fin n), Sopt.card = k → (gram V Sopt).PosDef →
      pvsExpect V μ (fun S => aObj (gram V (pad S))) ≤ α * aObj (gram V Sopt)) ∧
    ∃ S : Finset (Fin n), S.card = k ∧ (gram V S).PosDef ∧
      aObj (gram V S) ≤ α * aObj (weightedGram V x) := by sorry

end PropVolSampling.Reduction
