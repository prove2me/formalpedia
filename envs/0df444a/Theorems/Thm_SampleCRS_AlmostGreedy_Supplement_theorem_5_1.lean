-- Prove2me | Theorems.Thm_SampleCRS_AlmostGreedy_Supplement_theorem_5_1
-- name    : SampleCRS.AlmostGreedy.Supplement.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:42:24.355849+00:00
-- url     : https://prove2.me/theorems/59861137-5d14-41da-a58d-6e6233057d88
-- title:
--   Theorem 5.1 — finite-sample gap below the adversarial optimum
-- statement:
--   Fix any $k\ge2$, any finite sample bound $m\ge0$ and any family of randomized online capacity-$k$ policies using at most $m$ independent samples per element. They may know the fixed arrival order beforehand, but not $p$. There is a finite instance with $p\in[0,1]^n$ and exact mass $\sum_i p_i=k$ such that
--   $$\min_{i:p_i>0} C_{i,\pi}(p)<\gamma_{\rm adv}(k).$$
--   Here $\gamma_{\rm adv}(k)$ is the operational optimum for schemes that know $p$, rather than the random-order constant $\gamma_k$. The policy family precedes the choice of the bad instance. Padding unused samples covers every bound of at most $m$, including zero.
--
--   Differences from the source:
--   - encoding: arbitrary randomized nonanticipating policies, even with fixed order known in advance → real behavioral kernels on complete activation/action histories in arrival-position labels; reason: perfect recall on the finite observation tree represents arbitrary independent private randomness; relabelling a known order preserves all information
--   - encoding: the minimum conditional acceptance is strictly below γ → there exists a positive-bias element with Pr[A_i]<γ p_i; reason: on a finite exact-positive-mass instance these formulations are equivalent and avoid an empty-set minimum
-- source:
--   Shaddin Dughmi, Vasilis Livanos, Pranav Nuti, STOC 2027 submission #686 (October 2026), Theorem 5.1, p. 22

import Mathlib
import Definitions.Def_SampleCRS_AlmostGreedy_Supplement_sampleModel

namespace SampleCRS.AlmostGreedy.Supplement

/-- Theorem 5.1, p.22. finite-sample gap below the adversarial optimum. -/
theorem theorem_5_1 (k m : ℕ) (hk : 2 ≤ k) (π : ∀ n : ℕ, SamplePolicy n m) :
    ∃ (n : ℕ) (p : Fin n → ℝ), ValidProb p ∧ (∑ i, p i) = (k : ℝ) ∧
      ∃ i : Fin n, 0 < p i ∧ sampleAccept k (π n) p i < gammaAdv k * p i := by sorry

end SampleCRS.AlmostGreedy.Supplement
