-- Prove2me | Theorems.Thm_WalledBrauer_SuperSchurWeyl_lemma_7_3
-- name    : WalledBrauer.SuperSchurWeyl.lemma_7_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:15:58.71797+00:00
-- url     : https://prove2.me/theorems/249b4f89-1efe-4fa2-9409-1c7207226acc
-- title:
--   Lemma 7.3 — the right ℂΣ_{r+s}-action (7.6) on V^{⊗(r+s)}, (a b) acting as Ω_{a,b}
-- statement:
--   Let $N \ge 0$ and let $\Sigma_N$ act on $V^{\otimes N}$ by the formula (7.6),
--
--   $$
--   v_{\mathbf i} \cdot \sigma = \sum_{\mathbf j \in I^N} \mathrm{wt}({}_{\mathbf i}\sigma_{\mathbf j})\, v_{\mathbf j},
--   $$
--
--   where $\mathrm{wt}$ is the weight (7.5) of the permutation diagram of $\sigma$. Write $\Phi(\sigma)$ for the operator $v_{\mathbf i} \mapsto v_{\mathbf i} \cdot \sigma$. Then:
--
--   1. this is a right $\mathbb C\Sigma_N$-module structure: $\Phi(1) = 1$ and $\Phi(\sigma\tau) = \Phi(\tau)\Phi(\sigma)$ for all $\sigma, \tau \in \Sigma_N$, where $\sigma\tau = \sigma \circ \tau$;
--   2. for $1 \le a < b \le N$ the transposition $(a\ b)$ acts as the operator $\Omega_{a,b}$ of (7.3);
--   3. hence every $\Phi(\sigma)$ commutes with the action of $\mathfrak g = \mathfrak{gl}_{m|n}(\mathbb C)$: $\Phi(\sigma) \in \operatorname{End}_{\mathfrak g}(V^{\otimes N})$.
--
--   This is the super version of the classical place-permutation action, with the Koszul signs built into the weight.
--
--   **Formalization Note** `PhiDiag m n σ` is the matrix of $\Phi(\sigma)$ with column = input, so a right action is the identity `PhiDiag (σ * τ) = PhiDiag τ * PhiDiag σ`, with Mathlib's `σ * τ = σ ∘ τ` (which is the paper's product: the permutation diagram of $\sigma$ drawn under that of $\tau$). Positions are 0-based.
-- source:
--   Brundan and Stroppel, Gradings on walled Brauer algebras and Khovanov's arc algebra, arXiv:1107.0999v1, p. 51, Lemma 7.3 and (7.6)

import Mathlib
import Definitions.Def_WalledBrauer_SuperSchurWeyl_Weights

namespace WalledBrauer.SuperSchurWeyl

/-- Lemma 7.3 (p. 51): (7.6) defines a right `ℂΣ_N`-module structure on `V^{⊗ N}`
(`PhiDiag 1 = 1` and `PhiDiag (σ * τ) = PhiDiag τ * PhiDiag σ`, column = input); the
transposition `(a b)` acts as `Ω_{a,b}`; and every `σ` acts by an element of `End_g`. -/
theorem lemma_7_3 (m n N : ℕ) :
    PhiDiag m n (1 : Equiv.Perm (Fin N)) = 1 ∧
    (∀ σ τ : Equiv.Perm (Fin N), PhiDiag m n (σ * τ) = PhiDiag m n τ * PhiDiag m n σ) ∧
    (∀ a b : Fin N, a < b → PhiDiag m n (Equiv.swap a b) = Omega m n (allV N) a b) ∧
    (∀ σ : Equiv.Perm (Fin N), PhiDiag m n σ ∈ EndG m n (allV N)) := by sorry

end WalledBrauer.SuperSchurWeyl
