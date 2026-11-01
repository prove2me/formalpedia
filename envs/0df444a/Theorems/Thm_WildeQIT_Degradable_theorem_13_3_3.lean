-- Prove2me | Theorems.Thm_WildeQIT_Degradable_theorem_13_3_3
-- name    : WildeQIT.Degradable.theorem_13_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:57:06.296472+00:00
-- url     : https://prove2.me/theorems/610ff136-b721-4637-9373-97db1d8d6bf4
-- title:
--   Theorem 13.3.3 — Holevo information is concave in the input distribution
-- statement:
--   **Theorem 13.3.3.** Let $\mathcal N$ be a quantum channel, $\{\rho_x\}$ fixed signal states (density operators) indexed by a finite alphabet, $p_X$, $q_X$ probability distributions on that alphabet and $0\le\lambda\le1$. Put
--
--   $$
--   \sigma_{XB}\equiv\sum_x p_X(x)|x\rangle\langle x|_X\otimes\mathcal N(\rho_x),\quad
--   \tau_{XB}\equiv\sum_x q_X(x)|x\rangle\langle x|_X\otimes\mathcal N(\rho_x),
--   $$
--
--   $$
--   \omega_{XB}\equiv\sum_x\bigl[\lambda p_X(x)+(1-\lambda)q_X(x)\bigr]|x\rangle\langle x|_X\otimes\mathcal N(\rho_x).
--   $$
--
--   Then
--
--   $$
--   \lambda I(X;B)_\sigma+(1-\lambda)I(X;B)_\tau\le I(X;B)_\omega .
--   $$
--
--   With the signal states fixed, the Holevo information is a concave function of the input distribution, so for a classical–quantum channel its maximization is a concave program.
--
--
--   **Formalization Note** Finite-dimensional systems are matrices over finite index types (the book's setting); entropies are the published von Neumann entropy `QAlgorithms.vnEntropy` in bits; bipartite systems are product index types in the Kronecker convention.
--
--   Differences from the source:
--   - encoding: a quantum channel N (linear, completely positive, trace-preserving map) → WildeQIT.QChannel, a finite Kraus family K_i with sum K_i^† K_i = I; reason: every finite-dimensional channel has such a Kraus form (Theorem 4.4.1); same instances
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 13.3.3, eqs. (13.109)–(13.112), p. 405

import Definitions.Def_WildeQIT_Degradable_cqState
import Definitions.Def_DattaDiscord_mutualInfo
import Definitions.Def_WildeQIT_FinDist
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_QChannel

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 13.3.3, p. 405.
-/

namespace WildeQIT.Degradable

/-- **Theorem 13.3.3** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 405, eqs. (13.109)–(13.112)). The Holevo information `I(X; B)`
is concave in the input distribution when the signal states are fixed:
`λ I(X; B)_σ + (1 − λ) I(X; B)_τ ≤ I(X; B)_ω`, where
`σ_{XB} ≡ ∑ₓ p_X(x)|x⟩⟨x|_X ⊗ N(ρˣ)`, `τ_{XB} ≡ ∑ₓ q_X(x)|x⟩⟨x|_X ⊗ N(ρˣ)`,
`ω_{XB} ≡ ∑ₓ [λ p_X(x) + (1 − λ) q_X(x)]|x⟩⟨x|_X ⊗ N(ρˣ)`, and `0 ≤ λ ≤ 1`.

**Formalization Note.** `X` is any finite alphabet, `p`, `q` are probability distributions on it,
the signal states `ρˣ` are density operators, and `lam` is the book's `λ`. -/
theorem theorem_13_3_3 {X a b : Type} [Fintype X] [DecidableEq X] [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (N : QChannel a b) (ρ : X → Matrix a a ℂ)
    (hρ : ∀ x, IsDensityOperator (ρ x)) (p q : FinDist X) (lam : ℝ) (hlam0 : 0 ≤ lam)
    (hlam1 : lam ≤ 1) :
    lam * DattaDiscord.mutualInfo (cqState p.prob fun x => N.apply (ρ x)) +
        (1 - lam) * DattaDiscord.mutualInfo (cqState q.prob fun x => N.apply (ρ x)) ≤
      DattaDiscord.mutualInfo (cqState (fun x => lam * p.prob x + (1 - lam) * q.prob x)
        fun x => N.apply (ρ x)) := by sorry

end WildeQIT.Degradable
