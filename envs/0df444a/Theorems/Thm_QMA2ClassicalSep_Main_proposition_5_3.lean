-- Prove2me | Theorems.Thm_QMA2ClassicalSep_Main_proposition_5_3
-- name    : QMA2ClassicalSep.Main.proposition_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:02:55.063765+00:00
-- url     : https://prove2.me/theorems/982b1350-0b55-4d06-a4c0-b1ab8b532ed9
-- title:
--   Proposition 5.3 — NO instances: $\lambda_{\mathrm{sep}}(H)\ge1/4$ with probability $1-e^{-\Omega(N)}$
-- statement:
--   Let $k\ge2$, $N=2^k$, $K=N^2$, $\mu=N$, $\varepsilon_0=1/40$.
--
--   1. For every **good** NO parameter $\omega_-$ — in $\operatorname{supp}\mathcal D_-$, with $\theta\in\Theta_{\mathrm{size}}$ and $\|\Gamma-\bar\Gamma\|\le1/8$ — the Hamiltonian satisfies $\lambda_{\mathrm{sep}}(H)\ge1/4$.
--   2. Over $H\sim\mathcal D_-$,
--   $$
--   \Pr\big[\lambda_{\mathrm{sep}}(H)<\tfrac14\big]\le4K\exp(-\varepsilon_0^2\mu/3)+2N^6\exp(-N/2048).
--   $$
--
--   Since $K=N^2$, the right-hand side is $e^{-\Omega(N)}$: with probability $1-e^{-\Omega(N)}$ an instance of $\mathcal D_-$ is a NO instance of Problem 4.1.
--
--   Differences from the source:
--   - generalization: with probability 1 − exp(−Ω(N)) over H ∼ 𝒟₋, λ_sep(H) ≥ 1/4 → (a) every good NO parameter has λ_sep ≥ 1/4 for every k ≥ 2; (b) the failure probability is at most 4K e^{−ε₀²μ/3} + 2N⁶ e^{−N/2048} for every k ≥ 2; reason: (b) is the explicit bound of the proof and implies the printed asymptotic statement; (a) is the deterministic fact the proof establishes and that Theorem 6.1 and Appendix B use
-- source:
--   Sabee Grewal, Saachi Mutreja, Kabir Tomer, A classical oracle separation between QMA and QMA(2), STOC 2027 submission #618 (October 2026), SHA-256 79883d9d08b98b41b1bb600a6644f3f578ecb803702383a9f2a58d5bc7dacedf, pp. 21–23, Proposition 5.3 and its proof; good parameters, p. 24

import Definitions.Def_QMA2ClassicalSep_Main_HardDist

namespace QMA2ClassicalSep.Main

theorem proposition_5_3 (k : ℕ) (hk : 2 ≤ k) :
    (∀ ω : NOParam k, IsGood ω → 1 / 4 ≤ lamSep (noInst ω).Ham) ∧
    probNo (k := k) (fun ω => lamSep (noInst ω).Ham < 1 / 4) ≤
      4 * KK k * Real.exp (-(eps0 ^ 2 * mu k) / 3) +
        2 * ((2 : ℝ) ^ k) ^ 6 * Real.exp (-((2 : ℝ) ^ k) / 2048) := by sorry

end QMA2ClassicalSep.Main
