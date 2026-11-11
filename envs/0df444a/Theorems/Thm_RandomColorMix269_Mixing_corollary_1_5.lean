-- Prove2me | Theorems.Thm_RandomColorMix269_Mixing_corollary_1_5
-- name    : RandomColorMix269.Mixing.corollary_1_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:02:41.134138+00:00
-- url     : https://prove2.me/theorems/1fa94a97-d2d9-48ec-a478-928f02246172
-- title:
--   Corollary 1.5 — $\mu_{G,q}$ is $O_{\eta,d}(\ln n)$-spectrally independent w.h.p.
-- statement:
--   Fix $\eta\in(0,1)$. There is $d_0>1$ such that for every real $d\ge d_0$ there is $C=C(\eta,d)>0$ such that for every integer $q\ge(1+\eta)d$, with probability tending to $1$ over $G\sim G(n,d/n)$, $G$ is $q$-colourable and for every feasible pinning $\tau$ of $\mu_{G,q}$
--   $$
--   \lambda_{\max}\big(\Psi^\tau_{\mu_{G,q}}\big)\le C\ln n .
--   $$
--   Here $\Psi^\tau$ is the influence matrix of Definition 1.2. This bound is the spectral-independence hypothesis of the entropy-factorization theorem (Theorem 5.7) used in §5.
--
--   Differences from the source:
--   - encoding: vertex set [n] and colour set [q] → Fin n and Fin q; reason: relabelling only
--   - encoding: statements about the uniform law µ_{G,q}, defined only when G has a proper q-colouring → the high-probability event also contains Colorable G q; reason: without it the zero mass function makes the pinned conditions vacuous; µ_{G,q} is meaningless otherwise
--   - encoding: with probability at least 1 − o_n(1) over G ∼ G(n,d/n), for all sufficiently large n → the probability of the event under LPCommunity.SBMRecovery.erProb n (d/n) tends to 1; reason: the published law clamps d/n to [0,1], which differs from G(n,d/n) only for the finitely many n < d
--   - encoding: λ_max(Ψ^τ_µ) ≤ γ → z^T M z ≤ γ‖z‖² for M = D^{1/2} Ψ^τ_µ D^{-1/2}, D = diag of the one-site probabilities; reason: M is symmetric and similar to Ψ^τ_µ, so it has the same real spectrum; the empty matrix (all sites pinned) imposes nothing
--   - encoding: O_{η,d}(ln n)-spectrally independent → (C ln n)-spectrally independent for one C>0 chosen from η and d before q and n; reason: the meaning of the O-constant; the paper's proof gives C_SI = 2 C_CI
-- source:
--   Zhidan Li, Kuan Yang, STOC 2027 submission #269 (October 2026), PDF sha256 467638f1abc0f57df1bc0dcd9abfd308eb90ddbaf4947dac3eefa5f293ac6f05, p.4, Corollary 1.5

import Definitions.Def_RandomColorMix269_Mixing_Independence

open scoped Classical BigOperators
set_option autoImplicit false

namespace RandomColorMix269.Mixing

/-- Corollary 1.5, p.4. C depends only on η and d. -/
theorem corollary_1_5 :
    ∀ η : ℝ, 0 < η → η < 1 → ∃ d₀ : ℝ, 1 < d₀ ∧
      ∀ d : ℝ, d₀ ≤ d → ∃ C : ℝ, 0 < C ∧
        ∀ q : ℕ, (1 + η) * d ≤ q →
          WithHighProbability d (fun n G => Colorable G q ∧
            SpectralIndependent (MarkovMixing.properColoringDist G q) (C * Real.log n)) := by sorry

end RandomColorMix269.Mixing
