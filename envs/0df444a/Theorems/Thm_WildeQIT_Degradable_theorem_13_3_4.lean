-- Prove2me | Theorems.Thm_WildeQIT_Degradable_theorem_13_3_4
-- name    : WildeQIT.Degradable.theorem_13_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:57:15.993001+00:00
-- url     : https://prove2.me/theorems/69987d05-0b13-4aa0-85c8-7a5f6fa50756
-- title:
--   Theorem 13.3.4 — Holevo information is convex in the signal states
-- statement:
--   **Theorem 13.3.4.** Let $\mathcal N$ be a quantum channel, $p_X$ a probability distribution on a finite alphabet, $\{\sigma_x\}$ and $\{\tau_x\}$ two families of density operators indexed by that alphabet and $0\le\lambda\le1$. Put
--
--   $$
--   \sigma_{XB}\equiv\sum_x p_X(x)|x\rangle\langle x|_X\otimes\mathcal N(\sigma_x),\quad
--   \tau_{XB}\equiv\sum_x p_X(x)|x\rangle\langle x|_X\otimes\mathcal N(\tau_x),
--   $$
--
--   $$
--   \omega_{XB}\equiv\sum_x p_X(x)|x\rangle\langle x|_X\otimes\mathcal N\bigl(\lambda\sigma_x+(1-\lambda)\tau_x\bigr).
--   $$
--
--   Then
--
--   $$
--   \lambda I(X;B)_\sigma+(1-\lambda)I(X;B)_\tau\ge I(X;B)_\omega .
--   $$
--
--   With the input distribution fixed, the Holevo information is a convex function of the signal states; together with Theorem 13.3.3 this explains why maximizing the Holevo information of a general channel is hard.
--
--
--   **Formalization Note** Finite-dimensional systems are matrices over finite index types (the book's setting); entropies are the published von Neumann entropy `QAlgorithms.vnEntropy` in bits; bipartite systems are product index types in the Kronecker convention.
--
--   Differences from the source:
--   - encoding: a quantum channel N (linear, completely positive, trace-preserving map) → WildeQIT.QChannel, a finite Kraus family K_i with sum K_i^† K_i = I; reason: every finite-dimensional channel has such a Kraus form (Theorem 4.4.1); same instances
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 13.3.4, eqs. (13.115)–(13.118), pp. 405–406

import Definitions.Def_WildeQIT_Degradable_cqState
import Definitions.Def_DattaDiscord_mutualInfo
import Definitions.Def_WildeQIT_FinDist
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_QChannel

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 13.3.4, pp. 405–406.
-/

namespace WildeQIT.Degradable

/-- **Theorem 13.3.4** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, pp. 405–406, eqs. (13.115)–(13.118)). The Holevo information
`I(X; B)` is convex in the signal states when the input distribution is fixed:
`λ I(X; B)_σ + (1 − λ) I(X; B)_τ ≥ I(X; B)_ω`, where
`σ_{XB} ≡ ∑ₓ p_X(x)|x⟩⟨x|_X ⊗ N(σˣ)`, `τ_{XB} ≡ ∑ₓ p_X(x)|x⟩⟨x|_X ⊗ N(τˣ)`,
`ω_{XB} ≡ ∑ₓ p_X(x)|x⟩⟨x|_X ⊗ N(λσˣ + (1 − λ)τˣ)`, and `0 ≤ λ ≤ 1`.

**Formalization Note.** `X` is any finite alphabet, `p` a probability distribution on it, the
signal states `σˣ`, `τˣ` are density operators, and `lam` is the book's `λ`. -/
theorem theorem_13_3_4 {X a b : Type} [Fintype X] [DecidableEq X] [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (N : QChannel a b) (σ τ : X → Matrix a a ℂ)
    (hσ : ∀ x, IsDensityOperator (σ x)) (hτ : ∀ x, IsDensityOperator (τ x)) (p : FinDist X)
    (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    DattaDiscord.mutualInfo (cqState p.prob fun x =>
        N.apply ((lam : ℂ) • σ x + (1 - (lam : ℂ)) • τ x)) ≤
      lam * DattaDiscord.mutualInfo (cqState p.prob fun x => N.apply (σ x)) +
        (1 - lam) * DattaDiscord.mutualInfo (cqState p.prob fun x => N.apply (τ x)) := by sorry

end WildeQIT.Degradable
