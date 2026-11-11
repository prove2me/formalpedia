-- Prove2me | Theorems.Thm_RAREPricing_Existence_lemma_5
-- name    : RAREPricing.Existence.lemma_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:25:58.640607+00:00
-- url     : https://prove2.me/theorems/85dce19d-2137-403f-834b-7b4ac749b784
-- title:
--   Lemma 5 — security parameters: pricing at σ_j guarantees revenue ρ_j
-- statement:
--   Fix a market and a setting (constant $\nu$). For every seller $j$ there are constants $\rho_j>0$ and $\sigma_j\ge\rho_j/\nu$ such that for every response $q_{-j}\in\mathbb R^{[m]\setminus\{j\}}_{\ge0}$ and every allocation $x\in\mathrm{Dem}((\sigma_j,q_{-j}))$,
--   $$R_j((\sigma_j,q_{-j}),x)\ge\rho_j .$$
--   That is, a security pair $(\rho_j,\sigma_j)$ (definition item) exists.
--
--   Differences from the source:
--   - encoding: $(\sigma_j,q_{-j})$ with $q_{-j}\ge0$ → `Function.update r j σj` with $r_k\ge0$ for $k\ne j$; reason: the $j$-th entry of `r` is overwritten, so the same price vectors.
-- source:
--   Chaudhury, Garg, Huang, Sharma, RARE: Response-Aware Rational Equilibrium in Budget-Constrained Pricing Games, STOC 2027 submission (manuscript sha256 e9bb863f…), p. 20 (PDF 22), Lemma 5 (proof p. 29, PDF 31)

import Mathlib
import Definitions.Def_RAREPricing_Existence_Model

namespace RAREPricing.Existence

theorem lemma_5 {n m : ℕ} (M : Market n m) (s : Setting) (j : Fin m) :
    ∃ ρj σj : ℝ, IsSecurityPair M s j ρj σj := by sorry

end RAREPricing.Existence
