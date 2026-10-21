-- Prove2me | Theorems.Thm_PlatformLeakage_Perfect_proposition_3
-- name    : PlatformLeakage.Perfect.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:41:28.74495+00:00
-- url     : https://prove2.me/theorems/7a2c43d7-8014-4d02-87e0-c09cd9813bd5
-- title:
--   Proposition 3, pp. 18–19 — at the platform's optimal payout ratios, j-type providers leak off-platform iff Ro ∈ (a^j, b^j)
-- statement:
--   Consider the perfect-information on-demand platform model under its standing assumptions, with the leakage interval $\mathcal I^j=(a^j,b^j)$ of type $j$,
--   $$a^j=v^j+c\phi\left(1-\left(\Big(1-\sqrt{\tfrac{N^j-1}{N^j}}\Big)\sqrt{1+\tfrac{N^jv^j}{c\phi}}+\sqrt{\tfrac{N^j-1}{N^j}}\right)^2\right),\qquad b^j=v^j+c\phi\left(1-\Big(1+\sqrt{\tfrac{K^j}{c\phi\mu}}\Big)^2\right).$$
--   Then:
--   1. the platform's problem (15) has an optimal payout pair $(\omega^h,\omega^l)\in[0,1]^2$;
--   2. for every optimal payout pair and each type $j$, a selected provider participation equilibrium exists at $\omega^j$, and in every such equilibrium $(N^j_p,N^j_o)$, provided $R_o\ne a^j$ and $R_o\ne b^j$,
--   $$N^j_o>0\iff R_o\in\mathcal I^j;$$
--   3. at the payout ratio $\omega^{j*}$ of (23), every selected participation equilibrium $(N^j_p,N^j_o)$ satisfies, provided $R_o\ne b^j$,
--   $$N^j_o(\omega^{j*})>0\iff R_o\in\mathcal I^j. \tag{25}$$
--
--   In equilibrium, $j$-type providers leave for off-platform service exactly when the counterparty risk is high enough that keeping them no longer pays for the platform ($R_o>a^j$) but low enough that customers still value off-platform service above the providers' outside option ($R_o<b^j$).
--
--   **Formalization Note** "In equilibrium" is read as backward induction: customers' demand (5), the providers' selected participation equilibrium (Definition 1 with the selection rule of p. 16), and an optimal payout pair of (15). At $R_o=b^j$ the off-platform utility is $0$ (when $K^j>0$), and Definition 1 then sends non-platform providers off the platform, so the endpoint $b^j$ is excluded. At $R_o=a^j<b^j$ the platform is indifferent between keeping and losing the $j$-types, so an optimal pair may cause leakage; the every-optimum clause excludes $R_o=a^j$, while $\omega^{j*}$ of (23) breaks this tie towards keeping them.
-- source:
--   He, Savin, Goh & Teo, Off-Platform Threats in On-Demand Services, SSRN working paper 3550646 (PDF of 2021-03-25), pp. 18–19 (PDF 18–19), Proposition 3, (25); proof, Appendix pp. 4–5 (PDF 39–40)

import Mathlib
import Definitions.Def_PlatformLeakage_Perfect_Model

namespace PlatformLeakage.Perfect

/-- Proposition 3 (pp. 18–19): the platform's problem (15) has an optimal payout pair; at every optimal
pair `ω` and for each type `j`, a selected participation equilibrium exists, and in it some `j`-type
providers transact off the platform iff `R_o ∈ (a^j, b^j)` (when `R_o ∉ {a^j, b^j}`); at the payout
ratio `ω^{j*}` of (23) the same equivalence holds whenever `R_o ≠ b^j`. -/
theorem proposition_3 (P : Params) (hP : P.Std) :
    (∃ ω : PType → ℝ, IsOptimalPayout P ω) ∧
    (∀ ω : PType → ℝ, IsOptimalPayout P ω → ∀ j : PType,
      (∃ Np No : ℕ, IsSelectedEq P j (ω j) Np No) ∧
      ∀ Np No : ℕ, IsSelectedEq P j (ω j) Np No → P.Ro ≠ leakLo P j → P.Ro ≠ leakHi P j →
        (0 < No ↔ P.Ro ∈ Set.Ioo (leakLo P j) (leakHi P j))) ∧
    (∀ j : PType, ∀ Np No : ℕ, IsSelectedEq P j (omegaStar P j) Np No → P.Ro ≠ leakHi P j →
        (0 < No ↔ P.Ro ∈ Set.Ioo (leakLo P j) (leakHi P j))) := by sorry

end PlatformLeakage.Perfect
