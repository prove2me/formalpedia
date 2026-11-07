-- Prove2me | Theorems.Thm_RobustKellyTV_theorem_2_6
-- name    : RobustKellyTV.theorem_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:34:55.62174+00:00
-- url     : https://prove2.me/theorems/785ebd7b-91d3-49f7-b01a-354ab78480cc
-- title:
--   Theorem 2.6 — pathwise regret of adaptive clipped Kelly: $0\le\log W^\star_n-\log M^{\mathrm{CK}}_n=n\Gamma(\bar S_n)-\log M^{\mathrm{CK}}_n\le\log\binom{n+d-1}{d-1}$
-- statement:
--   Assume the standing assumptions and the Laplace pseudocounts. For every observation sequence $x_1,x_2,\dots\in\{1,\dots,d\}$ and every $n\ge1$, let $\bar S_{n,i}=N_i(n)/n$ and let
--
--   $$W^\star_n=\max_{E\in\mathcal E_0}\prod_{t=1}^nE(x_t)$$
--
--   (the maximum exists). Then
--
--   $$0\le\log W^\star_n-\log M^{\mathrm{CK}}_n=n\Gamma(\bar S_n)-\log M^{\mathrm{CK}}_n\le\log\binom{n+d-1}{d-1}.$$
--
--   The predictable procedure nearly matches the best fixed null-valid factor chosen in hindsight, for every sequence.
--
--   Differences from the source:
--   - encoding: W⋆_n := max_{E∈E0} Π_t E(x_t) → W⋆_n is the greatest element (IsGreatest) of the set of values {Π_t E(x_t) : E ∈ E0}; reason: states that the maximum is attained, as the paper's max asserts
--   - encoding: observation sequence x_1, x_2, … → x : ℕ → Fin d with x_t the coordinate t − 1; reason: indexing only
-- source:
--   A. Saha, A. Ramdas, Beyond least-favorable distribution pairs: asymptotically instance-optimal robust hypothesis testing, arXiv:2611.02130v1, §2.2, Theorem 2.6, p.9 (proof pp.24–26)

import Mathlib
import Definitions.Def_RobustKellyTV_kl
import Definitions.Def_RobustKellyTV_Mck

namespace RobustKellyTV

/-- **Theorem 2.6** (Pathwise regret of adaptive clipped Kelly). A. Saha, A. Ramdas, *Beyond least-favorable distribution pairs: asymptotically instance-optimal
robust hypothesis testing*, arXiv:2611.02130v1, Theorem 2.6, p.9.

Assume the Laplace pseudocounts (16). For every observation sequence `x₁, x₂, … ∈ X` and every
`n ≥ 1`, let `S̄_{n,i} = N_i(n)/n` and `W⋆_n = max_{E ∈ E0} Π_{t=1}^n E(x_t)`. Then
`0 ≤ log W⋆_n − log M^CK_n = nΓ(S̄_n) − log M^CK_n ≤ log C(n + d − 1, d − 1)`.

**Formalization Note.** Standing assumptions (p.6): `d ≥ 2`, `Pᵢ > 0`, `0 < ϵ0 < 1 − minᵢ Pᵢ`, bundled in `σ : Setting d`. Deterministic, for every `x : ℕ → Fin d` (observation `x_t` is
coordinate `t − 1`). The maximum is stated as `IsGreatest` of the set of values
`{Π_t E(x_t) : E ∈ E0}`, which also asserts that it is attained. `S̄_n` may have zero coordinates;
`Γ` uses the `[0, ∞]`-valued divergence there. -/
theorem theorem_2_6 {d : ℕ} (σ : Setting d) (x : ℕ → Fin d) (n : ℕ) (hn : 1 ≤ n) :
    ∃ Wstar : ℝ,
      IsGreatest ((fun E : Fin d → ℝ => ∏ t ∈ Finset.range n, E (x t)) '' eClass σ) Wstar ∧
      0 ≤ Real.log Wstar - Real.log (Mck σ (laplace d) n x) ∧
      Real.log Wstar - Real.log (Mck σ (laplace d) n x) =
        n * Gamma σ (empirical x n) - Real.log (Mck σ (laplace d) n x) ∧
      n * Gamma σ (empirical x n) - Real.log (Mck σ (laplace d) n x) ≤
        Real.log ((Nat.choose (n + d - 1) (d - 1) : ℕ) : ℝ) := by sorry

end RobustKellyTV
