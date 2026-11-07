-- Prove2me | Theorems.Thm_ReplicableOL_lemma_3_3
-- name    : ReplicableOL.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:49:37.153775+00:00
-- url     : https://prove2.me/theorems/97e7c366-0d15-408c-831c-1276302e5d1a
-- title:
--   Lemma 3.3 — moments of the construction
-- statement:
--   For all $k,L\ge1$ and $\Delta\in(0,\frac14]$:
--
--   (a) $\mathbb E|\sum_{j\le k}\mu_j|\ge\Delta\sqrt{2k/(3\pi)}-(2\Delta/\pi^2)\pi^{-k}\ge0.4606\Delta\sqrt k-0.2027\Delta\pi^{-k}$.
--
--   (b) $\mathbb Ex_j^4\le3\sigma_x^4$ and $\mathbb EX^4\le3s^4$, i.e. $\|X\|_4\le3^{1/4}s$; and $\mathbb E|\sum_jZ_j|\le\sqrt{kL}/2$.
--
--   (c) In the regime $k\ge100$, $\Delta\sqrt L\ge100$, with $\varsigma:=\Delta L\sqrt k$,
--   $$
--   A\ge0.4556\,\varsigma,\qquad s\le0.57738\,\varsigma,\qquad s_\mu=\varsigma/\sqrt3<0.57736\,\varsigma.
--   $$
--   These bounds fix the constant in the main theorem: $A\asymp\varsigma$ is the comparator's advantage and $\|X\|_4$ is of the same order.
--
--   Differences from the source:
--   - encoding: $A=\mathbb E|X|$ under Construction C → `E1 |Xterm|` in clause (c), with a conjunct equating it to `advantage T L Δ` for $k=\lfloor T/L\rfloor$; reason: the bridge from the measure-theoretic form to the finite form
--   - encoding: $\pi^{-k}$ → division by `Real.pi ^ k`; reason: same value
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Lemma 3.3, p.12

import Mathlib
import Definitions.Def_ReplicableOL_epochPrior
import Definitions.Def_ReplicableOL_advantage
import Definitions.Def_ReplicableOL_Bits
import Definitions.Def_ReplicableOL_E1
import Definitions.Def_ReplicableOL_eps
import Definitions.Def_ReplicableOL_Xterm
import Definitions.Def_ReplicableOL_sigmaXSq
import Definitions.Def_ReplicableOL_sSq
import Definitions.Def_ReplicableOL_sMuSq
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ReplicableOL

/-- **Lemma 3.3.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Lemma 3.3, p.12. All clauses, plus the bridge between `advantage` and `E1`.

**Formalization Note.** `ς := Δ L √k`, `π^{−k}` as division by `π^k`. The regime is `k ≥ 100`, `Δ√L ≥ 100` (p.10). `A` is `E1 |X|` here; the last conjunct identifies it with `advantage`. Decimal constants are the printed ones. -/
theorem lemma_3_3 {k L : ℕ} {Δ : ℝ} (hk : 1 ≤ k) (hL : 1 ≤ L) (hΔ : 0 < Δ) (hΔ' : Δ ≤ 1 / 4) :
    -- (a)
    Δ * √(2 * (k : ℝ) / (3 * Real.pi)) - (2 * Δ / Real.pi ^ 2) / Real.pi ^ k ≤
      ∫ θ, |∑ j : Fin k, θ j| ∂(epochPrior k Δ) ∧
    0.4606 * Δ * √(k : ℝ) - 0.2027 * Δ / Real.pi ^ k ≤
      Δ * √(2 * (k : ℝ) / (3 * Real.pi)) - (2 * Δ / Real.pi ^ 2) / Real.pi ^ k ∧
    -- (b)
    (∀ j : Fin k, E1 Δ (fun θ (S : Bits k L) => ((L : ℝ) * θ j + ∑ i : Fin L, eps θ S j i) ^ 4) ≤
      3 * sigmaXSq L Δ ^ 2) ∧
    E1 Δ (fun θ (S : Bits k L) => Xterm θ S ^ 4) ≤ 3 * sSq k L Δ ^ 2 ∧
    (E1 Δ (fun θ (S : Bits k L) => Xterm θ S ^ 4)) ^ (1 / 4 : ℝ) ≤ (3 : ℝ) ^ (1 / 4 : ℝ) * √(sSq k L Δ) ∧
    E1 Δ (fun θ (S : Bits k L) => |∑ j : Fin k, ∑ i : Fin L, eps θ S j i|) ≤ √((k : ℝ) * L) / 2 ∧
    -- (c)
    (100 ≤ k → 100 ≤ Δ * √(L : ℝ) →
      0.4556 * (Δ * L * √(k : ℝ)) ≤ E1 Δ (fun θ (S : Bits k L) => |Xterm θ S|) ∧
      √(sSq k L Δ) ≤ 0.57738 * (Δ * L * √(k : ℝ)) ∧
      √(sMuSq k L Δ) = (Δ * L * √(k : ℝ)) / √3 ∧
      (Δ * L * √(k : ℝ)) / √3 < 0.57736 * (Δ * L * √(k : ℝ))) ∧
    -- the two forms of `A`
    (∀ T : ℕ, advantage T L Δ = E1 Δ (fun θ (S : Bits (T / L) L) => |Xterm θ S|)) := by sorry

end ReplicableOL
