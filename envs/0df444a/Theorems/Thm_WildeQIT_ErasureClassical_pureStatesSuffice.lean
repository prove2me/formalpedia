-- Prove2me | Theorems.Thm_WildeQIT_ErasureClassical_pureStatesSuffice
-- name    : WildeQIT.ErasureClassical.pureStatesSuffice
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:37:48.08155+00:00
-- url     : https://prove2.me/theorems/bad5b8a8-8a18-46bb-b6f5-eb05b53a6d3b
-- title:
--   Theorem 13.3.2: pure states suffice for the Holevo information of a channel
-- statement:
--   Let $\mathcal N_{A\to B}$ be a quantum channel. Then
--
--   $$
--   \chi(\mathcal N)=\max_{\rho_{XA}}I(X;B)_\rho=\max_{\tau_{XA}}I(X;B)_\tau ,
--   $$
--
--   where $\rho_{XA}$ ranges over all classical–quantum inputs $\sum_x p_X(x)|x\rangle\langle x|_X\otimes\rho^x_A$ and $\tau_{XA}$ over those with pure signal states, $\tau_{XA}=\sum_x p_X(x)|x\rangle\langle x|_X\otimes|\varphi^x\rangle\langle\varphi^x|_A$, and $\rho_{XB},\tau_{XB}$ are obtained by sending the $A$ system through $\mathcal N_{A\to B}$. In particular the maximum over pure-state ensembles is attained.
--
--   It is enough to optimize the Holevo information over pure-state ensembles; this is how $\chi(\mathcal N)$ is defined in (20.8) and used in the proof that the erasure channel's Holevo information is additive.
--
--   **Formalization Note** The first equality is between the suprema over mixed-state and pure-state ensembles of any finite alphabet; the second conjunct gives a pure-state ensemble that attains the common value, which is the book's "max". The input space is nonempty.
--
--   Differences from the source:
--   - encoding: max over ρXA = max over τXA → the supremum over mixed ensembles equals the supremum over pure ensembles, and some pure ensemble attains it; reason: a maximum is a supremum that is attained; attainment by a pure ensemble also gives attainment of the mixed maximum
--   - encoding: a channel on a Hilbert space → a Kraus-form channel on a nonempty finite index type; reason: Hilbert spaces in the book are finite-dimensional and nonzero; every channel has a Kraus form (Theorem 4.4.1)
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 13.3.2, (13.104)–(13.105), p. 404

import Definitions.Def_WildeQIT_ErasureClassical_holevoInfo
import Definitions.Def_WildeQIT_ErasureClassical_holevoInfoMixed

namespace WildeQIT.ErasureClassical

/-- **Theorem 13.3.2** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8,
p. 404): "It is sufficient to maximize the Holevo information with respect to pure states:
`χ(N) = max_{ρ_{XA}} I(X; B)_ρ = max_{τ_{XA}} I(X; B)_τ` (13.104), where
`τ_{XA} ≡ ∑ₓ p_X(x)|x⟩⟨x|_X ⊗ |φˣ⟩⟨φˣ|_A` (13.105), and `ρ_{XB}` and `τ_{XB}` are the states that
result from sending the `A` system of `ρ_{XA}` and `τ_{XA}` through the quantum channel `N_{A→B}`,
respectively."

**Formalization Note.** The first conjunct is the equality of the supremum over mixed-state
ensembles (Definition 13.3.1) and the supremum over pure-state ensembles ((20.8)). The second
conjunct is the attainment the book's `max` asserts: some pure-state ensemble achieves the
common value (so the maximum over mixed ensembles is attained as well). The input space is
nonempty. -/
theorem pureStatesSuffice {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    [Nonempty a] (N : QChannel a b) :
    holevoInfoMixed N = holevoInfo N ∧
      ∃ e : PureEnsemble a, HolevoCQ.holevoChi (fun x => N.apply (e.state x)) e.p.prob = holevoInfo N := by sorry

end WildeQIT.ErasureClassical
