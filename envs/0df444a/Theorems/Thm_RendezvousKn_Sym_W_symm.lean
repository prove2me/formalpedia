-- Prove2me | Theorems.Thm_RendezvousKn_Sym_W_symm
-- name    : RendezvousKn.Sym.W_symm
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:39:01.802021+00:00
-- url     : https://prove2.me/theorems/ce6ea499-fafe-49ee-9fb5-a9bba816c610
-- title:
--   Symmetry of W and (2), proof of Theorem 1, p. 5 — W is symmetric and E T⟨σ, σ⟩ splits into passive/active parts
-- statement:
--   Fix $n\ge2$. (i) The function $W$ is symmetric: for all tactics $\tau_A,\tau_B$,
--   $$W(\tau_A,\tau_B)=W(\tau_B,\tau_A).$$
--   (ii) For every strategy $\sigma$ with probability vector $a$, write $a=a^{\mathbf P}+a^{\mathbf A}$, where $a^{\mathbf P}$ is $a$ restricted to passive tactics and $a^{\mathbf A}$ is $a$ restricted to active tactics (both zero elsewhere), and let $\Phi\langle x,y\rangle=\sum_{\tau_A,\tau_B}W(\tau_A,\tau_B)\,x_{\tau_A}y_{\tau_B}$. Then
--   $$\mathbb E\,T\langle\sigma,\sigma\rangle=\Phi\langle a,a\rangle=\Phi\langle a^{\mathbf P},a^{\mathbf P}\rangle+\Phi\langle a^{\mathbf A},a^{\mathbf A}\rangle+2\,\Phi\langle a^{\mathbf P},a^{\mathbf A}\rangle.\qquad(2)$$
--
--   The symmetry of $W$ is what lets the two mixed terms of the bilinear form be merged in (2), the decomposition on which the proof of Theorem 1 rests.
--
--   **Formalization Note** In Lean $\Phi\langle x,y\rangle$ is `expWait x y`, which is defined for arbitrary real vectors. As in the paper (p. 5), $a^{\mathbf P}$ is supported on the passive tactics, the set the paper denotes $\Theta^{\mathbf A}$.
--
--   Differences from the source:
--   - encoding: strategy σ ∈ Σ_n, a probability distribution on the tactics [n] → [n]; E T⟨σ_A, σ_B⟩ with independent draws → σ ∈ stdSimplex ℝ (Fin n → Fin n); expWait σ_A σ_B = Σ_{τ_A, τ_B} σ_A(τ_A) σ_B(τ_B) W(τ_A, τ_B); reason: a distribution on a finite set is its probability vector; the double sum is the expectation over independent τ_A ~ σ_A, τ_B ~ σ_B, π uniform (the paper's E T⟨σ_A, σ_B⟩ = Φ⟨a, b⟩, p. 4)
--   - encoding: expectation over a uniformly random binding π: [n] → [n]; rounds 1, …, n; locations [n] → average over all n! elements of Equiv.Perm (Fin n) (avgPerm); rounds and locations are Fin n, Lean round i being round i + 1; reason: the same finite uniform distribution and the same game; no instance changes
-- source:
--   Bonamy, Pilipczuk, Sereni, On the effect of symmetry requirement for rendezvous on the complete graph, arXiv:2002.03764v1, p. 5 (PDF 6), proof of Theorem 1, 'As W(·,·) is a symmetric function', equation (2)

import Mathlib
import Definitions.Def_RendezvousKn_Sym_Model

namespace RendezvousKn.Sym

theorem W_symm (n : ℕ) (hn : 2 ≤ n) :
    (∀ τA τB : Tactic n, W τA τB = W τB τA) ∧
    (∀ σ : Tactic n → ℝ, σ ∈ stdSimplex ℝ (Tactic n) →
      expWait σ σ =
        expWait (fun τ => if IsPassive τ then σ τ else 0) (fun τ => if IsPassive τ then σ τ else 0) +
        expWait (fun τ => if IsPassive τ then 0 else σ τ) (fun τ => if IsPassive τ then 0 else σ τ) +
        2 * expWait (fun τ => if IsPassive τ then σ τ else 0)
          (fun τ => if IsPassive τ then 0 else σ τ)) := by sorry

end RendezvousKn.Sym
