-- Prove2me | Theorems.Thm_QAlgorithms_DeWolf_adversary_claim4_tMinus_near_large_phase
-- name    : QAlgorithms.DeWolf.adversary_claim4_tMinus_near_large_phase
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:42:45.742822+00:00
-- url     : https://prove2.me/theorems/c79a0d29-8204-4107-a05e-035ab956bd5c
-- title:
--   |t⁻_x⟩ is close to the large-eigenphase part of U_x
-- statement:
--   In the setting of Claim 3 (a feasible solution $\{u_{xj}, v_{xj}\}$ of the dual SDP for $\mathrm{ADV}^{\pm}(f)$ with objective value $A > 0$, the states $|t^\pm_x\rangle$, $|\psi_y\rangle$, the projectors $\Lambda$, $\Pi_x$ and the unitary $U_x = (2\Pi_x - I)(2\Lambda - I)$), let $\Theta = 1/(1000A)$. For every $x \in D$ there is a vector $|\varphi\rangle$ in the span of the eigenvectors of $U_x$ whose eigenvalues $e^{i\theta}$, $\theta \in (-\pi, \pi]$, satisfy $|\theta| > \Theta$, such that
--
--   $$
--   \big\| |t^-_x\rangle - |\varphi\rangle \big\| \le \frac{1}{20} + \frac{1}{2000A}.
--   $$
--
--   Equivalently, the component of $|t^-_x\rangle$ in the eigenspaces of $U_x$ with eigenphase $|\theta| \le \Theta$ has norm at most $1/20 + 1/(2000A)$. Together with Claim 3, this lets phase estimation with precision $\Theta/2$ distinguish $|t^+_x\rangle$ from $|t^-_x\rangle$.
--
--   **Formalization Note** The eigenphase $\theta$ is the principal argument `Complex.arg`, which takes values in $(-\pi, \pi]$; the span of eigenvectors is the supremum of the eigenspaces of $U_x$ over the eigenvalues with $|\arg \mu| > \Theta$. The informal "close" is pinned to the bound the source's proof establishes, and it is stated for every $A > 0$ (the proof's own hypothesis; the source adds "we may assume $A \ge 1$" only to call the bound small).
-- source:
--   Ronald de Wolf, Quantum Computing: Lecture Notes, 27 August 2026, PDF p. 115, §12.3, Claim 4. https://homepages.cwi.nl/~rdewolf/qcnotes.pdf

import Definitions.Def_QAlgorithms_Defs_Adversary
set_option autoImplicit false

namespace QAlgorithms.DeWolf






/-- de Wolf §12.3, Claim 4 (PDF pp. 115–116): for a feasible dual solution with objective value
`A > 0` and every `x ∈ D`, the state `|t^-_x⟩` is within Euclidean distance
`1/20 + 1/(2000A)` of a superposition of eigenvectors of `U_x` whose eigenvalues `e^{iθ}`,
`θ ∈ (−π, π]`, have `|θ| > Θ = 1/(1000A)`. The distance bound is the one the source's proof
establishes. -/
theorem adversary_claim4_tMinus_near_large_phase {N : ℕ} (P : AdvAlg N)
    (hfeas : DualFeasibleDeWolf P.f P.D P.d P.u P.v) (hA : 0 < P.A) (x : P.D) :
    ∃ φ ∈ (⨆ μ ∈ {μ : ℂ | 1 / (1000 * P.A) < |Complex.arg μ|},
        Module.End.eigenspace
          ((P.walk x : AdvSpace N P.d →L[ℂ] AdvSpace N P.d) : AdvSpace N P.d →ₗ[ℂ] AdvSpace N P.d)
          μ),
      ‖P.tMinus x - φ‖ ≤ 1 / 20 + 1 / (2000 * P.A) := by
  sorry

end QAlgorithms.DeWolf
