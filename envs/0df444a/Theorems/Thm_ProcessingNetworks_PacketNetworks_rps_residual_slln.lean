-- Prove2me | Theorems.Thm_ProcessingNetworks_PacketNetworks_rps_residual_slln
-- name    : ProcessingNetworks.PacketNetworks.rps_residual_slln
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T20:02:57.596526+00:00
-- url     : https://prove2.me/theorems/5e952340-3e3b-4116-b3de-4f9bfeb4af75
-- title:
--   Lemma 12.23 — the class-level residual process vanishes almost surely (milestone)
-- statement:
--   **Lemma 12.23.** Let $\{z_\ell : \ell \ge 1\} \subset \mathbb Z^I_+$ satisfy $|z_\ell| \ge
--   \ell^2$ for each $\ell$, and let $\Omega_2 := \{\omega :
--   \lim_{\ell\to\infty}\xi^{z_\ell}(|z_\ell|,\omega)/|z_\ell| = 0\}$. Then $P(\Omega_2) = 1$.
--
--   This is the residual-process a.s. convergence result needed for Theorem 12.24's fluid-limit
--   drift equation, proved from the fact that $\xi^z_i$ (a partial sum of the bounded
--   martingale-difference sequence $s_i(\tau)-\hat s_i(\tau)$) obeys the strong law of large
--   numbers, together with the Borel–Cantelli lemma.
--
--   **Formalization note.** The setting is the chapter's: a fixed-routing packet network with
--   $S$ from (12.10), primitives satisfying Section 12.1's standing assumptions, and the random
--   proportional scheduler as the policy. The martingale-difference and boundedness properties
--   the book's proof invokes are consequences of that setting (they follow from the definition of
--   $\hat s$ and $s_i \le c_{\max}$), not hypotheses. The sequence index is 0-based.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 251 (PDF p. 267), Lemma 12.23, Eq. (12.64)

import Mathlib
import Definitions.Def_ProcessingNetworks_PacketNetworks_RPSResidualProcess

namespace ProcessingNetworks.PacketNetworks

open MeasureTheory ProbabilityTheory

/-- Lemma 12.23, Dai & Harrison p. 251 (PDF p. 267): in a fixed-routing packet network with
schedule set `S` from (12.10), operated under the random proportional scheduler (the policy of the
primitives `P`, which satisfy Section 12.1's standing stochastic assumptions with arrival rate
vector `λ`), let `{zₗ : ℓ ≥ 1} ⊂ Z^I_+` be a sequence of initial states with `|zₗ| ≥ ℓ²` for each
`ℓ ≥ 1` (0-indexed: `(ℓ+1)² ≤ |zseq ℓ|`) and let `Ω₂` be the set of sample paths on which
`ξ^{zₗ}(|zₗ|,ω)/|zₗ| → 0`. Then `P(Ω₂) = 1` (12.64). -/
theorem rps_residual_slln
    {I K : ℕ} {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (fr : FixedRoutingData I K) (S : Finset (Fin I → ℕ)) (hS : IsScheduleSet fr.cfg S)
    (lam : Fin I → ℝ) (P : PacketPrimitives I I Ω) (hP : PrimitiveAssumptions P lam)
    (hRPS : IsRPSPolicy fr S P.f)
    (zseq : ℕ → Fin I → ℕ) (hzseq : ∀ ℓ : ℕ, ((ℓ : ℝ) + 1) ^ 2 ≤ sizeN (zseq ℓ)) :
    ℙ (omega2 fr P zseq) = 1 := by sorry

end ProcessingNetworks.PacketNetworks
