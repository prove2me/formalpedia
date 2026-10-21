-- Prove2me | Theorems.Thm_ReputationLies_Matching_proposition_1
-- name    : ReputationLies.Matching.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:19:59.331036+00:00
-- url     : https://prove2.me/theorems/ee4336bb-a0a5-4d11-bda6-93c9c2a2f911
-- title:
--   Proposition 1, p. 14 (PDF 16) — the game has a unique equilibrium, in threshold strategies
-- statement:
--   Throughout, the standing assumptions of §2 hold: $0 < s_L < s_H < 1$, $p \in (0,1)$, $g(r) > 0$ and $c(r) \in (0,r)$ for $r > 0$, $v(0) = 0$ and $v' > 0$, Assumption (A1) $L' > 0$, and the bias and outside-option laws are continuous with full support on $[0,1]$, $F$ being $C^1$ on $[0,1]$.
--
--   Fix a reputation $r > 0$. The game has an equilibrium, and it is unique: any two equilibria have the same adviser strategy on bias types $b \in [0,1]$, the same firm strategy on outside values $x \in [0,1]$, and the same beliefs. Every equilibrium has the following form, for some threshold $b^* \in (0,1]$:
--   1. (i)(a) an adviser with a high-skilled candidate always recommends;
--   2. (i)(b) an adviser with a low-skilled candidate recommends (lies) if $b > b^*$ and does not recommend if $b \le b^*$;
--   3. (ii)(a) after no recommendation the firm's belief is $s_{NR} = s_L$, and it hires the focal candidate iff $x \le s_L$;
--   4. (ii)(b) after a recommendation the firm's belief is $s_R = s_R(b^*)$ of eq. (2), and it hires the focal candidate iff $x \le s_R(b^*)$;
--   5. $b^* = 1$ if and only if $L(r) \ge \bar B$, and if $b^* < 1$ then $b^*$ solves the threshold equation
--   $$b^*\,\frac{F(s_R(b^*)) - F(s_L)}{F(s_R(b^*))} = L(r). \tag{12}$$
--
--   Item 5 is the description of the cutoff given on p. 14 above the proposition and in Step 5 of its proof. The proposition is the basis of every comparative static in the paper.
--
--   **Formalization Note.** Uniqueness is stated on the supports $[0,1]$ of the bias and of the outside option; off the supports the strategies are payoff-irrelevant.
-- source:
--   Câmara, Jia & Raffiee, Reputation, competition, and lies in labor market recommendations, authors' manuscript of Sept. 26, 2022 (Management Science, doi:10.1287/mnsc.2022.4654), p. 14 (PDF 16), Proposition 1; cutoff description p. 14 (PDF 16) and proof of Proposition 1, Step 5, p. 39 (PDF 41)

import Mathlib
import Definitions.Def_ReputationLies_Matching_Model

open Set

namespace ReputationLies.Matching

/-- Proposition 1, p. 14: at every reputation `r > 0` the game has an equilibrium, it is unique
(on the bias types `[0, 1]` and outside-option types `[0, 1]`), and it has the threshold form:
high-skilled types always recommend, low-skilled types recommend iff `b > b∗` for some
`b∗ ∈ (0, 1]`; the firm believes `sL` after no recommendation and `sR(b∗)` after one, and hires
the focal candidate iff `x` is at most its belief; `b∗ = 1` iff `L(r) ≥ B̄`, and otherwise `b∗`
solves eq. (12). -/
theorem proposition_1 (P : Primitives) (hP : P.Standing) (r : ℝ) (hr : 0 < r) :
    (∃ σ : Profile, IsEquilibrium P σ r) ∧
    (∀ σ σ' : Profile, IsEquilibrium P σ r → IsEquilibrium P σ' r →
      (∀ b ∈ Icc (0 : ℝ) 1, ∀ hi, σ.σA b hi = σ'.σA b hi) ∧
      (∀ x ∈ Icc (0 : ℝ) 1, ∀ m, σ.σF x m = σ'.σF x m) ∧
      σ.sR = σ'.sR ∧ σ.sNR = σ'.sNR) ∧
    (∀ σ : Profile, IsEquilibrium P σ r → ∃ bstar ∈ Ioc (0 : ℝ) 1,
      (∀ b ∈ Icc (0 : ℝ) 1, σ.σA b true = true) ∧
      (∀ b ∈ Icc (0 : ℝ) 1, (σ.σA b false = true ↔ bstar < b)) ∧
      σ.sNR = P.sL ∧ (∀ x ∈ Icc (0 : ℝ) 1, (σ.σF x false = true ↔ x ≤ P.sL)) ∧
      σ.sR = P.sRof bstar ∧ (∀ x ∈ Icc (0 : ℝ) 1, (σ.σF x true = true ↔ x ≤ P.sRof bstar)) ∧
      (bstar = 1 ↔ P.Bbar ≤ P.L r) ∧ (bstar < 1 → P.lieGain bstar = P.L r)) := by sorry

end ReputationLies.Matching
