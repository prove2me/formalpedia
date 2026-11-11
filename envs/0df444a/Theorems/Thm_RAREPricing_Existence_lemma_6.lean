-- Prove2me | Theorems.Thm_RAREPricing_Existence_lemma_6
-- name    : RAREPricing.Existence.lemma_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:26:05.04329+00:00
-- url     : https://prove2.me/theorems/2b05c016-c11f-4bd8-b224-a6943b7a2e12
-- title:
--   Lemma 6 — overpricing parameter: above L_j against a competitor at price B, seller j earns ≤ ρ_j/(2κ)
-- statement:
--   Fix a market and a setting (constant $\kappa=B/(\nu\beta)$). Let $j$ be a seller and $(\rho_j,\sigma_j)$ any pair as in Lemma 5 ($\rho_j>0$, $\sigma_j\ge\rho_j/\nu$, and $R_j((\sigma_j,q_{-j}),x)\ge\rho_j$ for all $q_{-j}\ge0$, $x\in\mathrm{Dem}((\sigma_j,q_{-j}))$). Then there is $L_j\ge\max(B,\sigma_j)$ such that for all prices $q\in\mathbb R^m_{\ge0}$ and $x\in\mathrm{Dem}(q)$,
--   $$q_j>L_j\ \text{ and }\ \max_{k\ne j}q_k=B\ \Longrightarrow\ R_j(q,x)\le\frac{\rho_j}{2\kappa}.$$
--
--   Differences from the source:
--   - generalization: $\sigma_j,\rho_j$ "as in Lemma 5" (the constants its proof constructs) → every pair satisfying Lemma 5's conclusion; reason: the paper's constants are one such pair, so the statement specializes to it.
--   - encoding: $\max_{k\ne j}q_k=B$ → $q_k\le B$ for all $k\ne j$ and $q_k=B$ for some $k\ne j$; reason: equivalent, the index set being nonempty ($m\ge2$).
-- source:
--   Chaudhury, Garg, Huang, Sharma, RARE: Response-Aware Rational Equilibrium in Budget-Constrained Pricing Games, STOC 2027 submission (manuscript sha256 e9bb863f…), p. 20 (PDF 22), Lemma 6 (proof pp. 29–30, PDF 31–32)

import Mathlib
import Definitions.Def_RAREPricing_Existence_Model

namespace RAREPricing.Existence

theorem lemma_6 {n m : ℕ} (M : Market n m) (s : Setting) (j : Fin m) (ρj σj : ℝ)
    (hsec : IsSecurityPair M s j ρj σj) :
    ∃ Lj : ℝ, IsOverpricingBound M s j ρj σj Lj := by sorry

end RAREPricing.Existence
