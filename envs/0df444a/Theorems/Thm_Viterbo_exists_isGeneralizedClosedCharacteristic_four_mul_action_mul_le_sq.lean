-- Prove2me | Theorems.Thm_Viterbo_exists_isGeneralizedClosedCharacteristic_four_mul_action_mul_le_sq
-- name    : Viterbo.exists_isGeneralizedClosedCharacteristic_four_mul_action_mul_le_sq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-03T17:41:23.975993+00:00
-- url     : https://prove2.me/theorems/54be58ac-d306-4f0d-a656-6778dbca5c64
-- title:
--   Clarke's dual action principle (length form) — a generalized closed characteristic of minimal action bounds 4 A(γ) A(z) by the squared K-length of every loop z
-- statement:
--   Let $n \ge 1$ and let $K \subset \mathbb R^{2n}$ be a convex domain (bounded, convex, with nonempty interior). Then there is a non-constant generalized closed characteristic $\gamma$ on $\partial K$ (`Viterbo.IsGeneralizedClosedCharacteristic`, period $1$) such that, for every $1$-periodic absolutely continuous loop $z\colon \mathbb R \to \mathbb R^{2n}$ with positive action $A(z) > 0$,
--   $$4\,A(\gamma)\,A(z) \le \Big(\int_0^1 h_K(-J\dot z(t))\,dt\Big)^2,$$
--   where $A(z) = \tfrac12\int_0^1 \langle J z(t), \dot z(t)\rangle\,dt$ (`Viterbo.action`) and $h_K(u) = \sup_{x \in K}\langle x, u\rangle$ is the support function of $K$. Here "absolutely continuous" means $z(b) - z(a) = \int_a^b v$ for a locally integrable $v$, and $\dot z$ is the pointwise derivative, as in `Viterbo.action`.
--
--   This is the form of Clarke's dual action principle that the Viterbo mission uses; the source is S. Artstein-Avidan and Y. Ostrover, *Bounds for Minkowski billiard trajectories in convex bodies*, IMRN 2014, Proposition 2.7 (arXiv version pp. 8–9): "$\widetilde c_{\rm EHZ}(\Sigma) = \min_{z \in \mathcal E} \frac{\pi}{2}\int_0^{2\pi} h_\Sigma^2(\dot z(t))\,dt = \min \widetilde{\mathcal L}(\Sigma)$". Two differences from that sentence. First, it is stated with the length $\int h_K$ in place of the energy $\int h_K^2$, as in the proof of the paper's Theorem 2.8 ("with a power $p = 1$ in the integrand instead of $p = 2$"). The two forms agree after reparametrizing a loop to constant $h_K$-speed; for loops normalized to period $1$, the length form is the stronger one, by the Cauchy–Schwarz inequality. Second, $-J\dot z$ replaces $\dot z$: the substitution $z = -Jw$ preserves the action, so the two minima coincide.
-- source:
--   Artstein-Avidan, S. and Ostrover, Y., Bounds for Minkowski billiard trajectories in convex bodies, Int. Math. Res. Not. IMRN 2014, 165–193, https://doi.org/10.1093/imrn/rns216 (arXiv:1111.2353, whose page numbers are used), pp. 8–9, Proposition 2.7 (with Proposition 2.5 and Lemma 5.1), in length form

import Mathlib
import Definitions.Def_SymmetricPolar
import Definitions.Def_Viterbo

open MeasureTheory

namespace Viterbo

theorem exists_isGeneralizedClosedCharacteristic_four_mul_action_mul_le_sq (n : ℕ) (hn : 1 ≤ n)
    (K : Set (OAI.SymmetricPolar.Phase n)) (hK : IsConvexDomain K) :
    ∃ γ : ℝ → OAI.SymmetricPolar.Phase n, IsGeneralizedClosedCharacteristic K γ ∧
      (∃ s t, γ s ≠ γ t) ∧
      ∀ z : ℝ → OAI.SymmetricPolar.Phase n, Function.Periodic z 1 →
        (∃ v : ℝ → OAI.SymmetricPolar.Phase n, LocallyIntegrable v volume ∧
          ∀ a b, z b - z a = ∫ s in a..b, v s) →
        0 < action z →
        4 * action γ * action z ≤
          (∫ t in (0 : ℝ)..1, sSup ((fun x => phaseInner x (-J (deriv z t))) '' K)) ^ 2 := by
  sorry

end Viterbo
