-- Prove2me | Theorems.Thm_WildeQIT_Degradable_theorem_13_3_2
-- name    : WildeQIT.Degradable.theorem_13_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:58:36.501489+00:00
-- url     : https://prove2.me/theorems/57ba4b70-2250-41ad-853c-37eb5a473803
-- title:
--   Theorem 13.3.2 — pure-state ensembles suffice for the Holevo information
-- statement:
--   **Theorem 13.3.2.** Let $\mathcal N_{A\to B}$ be a quantum channel. It is sufficient to maximize the Holevo information with respect to pure states:
--
--   $$
--   \chi(\mathcal N)=\max_{\rho_{XA}} I(X;B)_\rho=\max_{\tau_{XA}} I(X;B)_\tau ,
--   $$
--
--   where $\tau_{XA}\equiv\sum_x p_X(x)|x\rangle\langle x|_X\otimes|\varphi_x\rangle\langle\varphi_x|_A$ ranges over pure-state ensembles, and $\rho_{XB}$, $\tau_{XB}$ are the states obtained by sending the $A$ system of $\rho_{XA}$, $\tau_{XA}$ through $\mathcal N_{A\to B}$.
--
--   This reduces the optimization defining the Holevo information of a channel to ensembles of pure signal states.
--
--
--   **Formalization Note** Finite-dimensional systems are matrices over finite index types (the book's setting); entropies are the published von Neumann entropy `QAlgorithms.vnEntropy` in bits; bipartite systems are product index types in the Kronecker convention.
--
--   Differences from the source:
--   - encoding: a quantum channel N (linear, completely positive, trace-preserving map) → WildeQIT.QChannel, a finite Kraus family K_i with sum K_i^† K_i = I; reason: every finite-dimensional channel has such a Kraus form (Theorem 4.4.1); same instances
--   - encoding: nonzero input Hilbert space (implicit throughout the book) → [Nonempty a] on the input index type; reason: an empty index type is a zero-dimensional space with no input state, where the book's maximum is undefined and Lean's supremum returns the junk value 0
--   - encoding: both χ(N) and the pure-state maximum defined as a maximum over inputs → both χ(N) and the pure-state maximum defined as a real supremum ⨆ over the same inputs; reason: the set of values is nonempty and bounded above, and the maximum is attained, so both give the same number
--   - encoding: χ(N) = max_ρ I(X;B)_ρ = max_τ I(X;B)_τ → holevoInfoChannel N = ⨆ τ : PureEnsemble a, I(X;B)_τ; reason: the first equality is Definition 13.3.1 (holevoInfoChannel is that maximum), so the content is the second equality
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 13.3.2, eqs. (13.104)–(13.105), p. 404

import Definitions.Def_WildeQIT_Degradable_holevoInfoChannel
import Definitions.Def_WildeQIT_Degradable_PureEnsemble

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 13.3.2, p. 404.
-/

namespace WildeQIT.Degradable

/-- **Theorem 13.3.2** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 404, eqs. (13.104)–(13.105)). It is sufficient to maximize the
Holevo information with respect to pure states:
`χ(N) = max_{ρ_{XA}} I(X; B)_ρ = max_{τ_{XA}} I(X; B)_τ`, where
`τ_{XA} ≡ ∑ₓ p_X(x)|x⟩⟨x|_X ⊗ |φˣ⟩⟨φˣ|_A` and `ρ_{XB}`, `τ_{XB}` result from sending the `A`
system through `N_{A→B}`.

**Formalization Note.** The input space is nonzero (`Nonempty a`), as every Hilbert space of the book is. The first equality is Definition 13.3.1 (`holevoInfoChannel`); the
statement is the second. Both maxima are suprema over inputs with a finite alphabet `Fin k` of
any size; both sets of values are bounded above by `log₂ |b|`. -/
theorem theorem_13_3_2 {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    [Nonempty a]
    (N : QChannel a b) :
    holevoInfoChannel N =
      ⨆ τ : PureEnsemble a,
        DattaDiscord.mutualInfo (cqState τ.p.prob fun x => N.apply (QAlgorithms.pureDensity (τ.φ x))) := by sorry

end WildeQIT.Degradable
