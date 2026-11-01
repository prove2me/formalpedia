-- Prove2me | Theorems.Thm_WildeQIT_HSW_theorem_13_3_2
-- name    : WildeQIT.HSW.theorem_13_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T19:13:27.068832+00:00
-- url     : https://prove2.me/theorems/25fbc424-7e61-4d3b-b6f2-3c1a7e797c88
-- title:
--   Theorem 13.3.2: pure states suffice, $\chi(\mathcal N) = \max_{\rho_{XA}} I(X;B)_\rho = \max_{\tau_{XA}} I(X;B)_\tau$
-- statement:
--   Let $\mathcal N_{A\to B}$ be a quantum channel between finite-dimensional Hilbert spaces. The maximum of the Holevo information over input ensembles of mixed states equals the maximum over ensembles of pure states:
--
--   $$
--   \chi(\mathcal N) = \max_{\rho_{XA}} I(X;B)_\rho = \max_{\tau_{XA}} I(X;B)_\tau ,
--   $$
--
--   where $\rho_{XA} = \sum_x p_X(x)|x\rangle\langle x|_X\otimes\rho^x_A$ ranges over classical–quantum states with arbitrary density operators $\rho^x_A$, $\tau_{XA} = \sum_x p_X(x)|x\rangle\langle x|_X\otimes|\varphi_x\rangle\langle\varphi_x|_A$ over those with pure states, both over arbitrary finite alphabets, and $\rho_{XB}$, $\tau_{XB}$ are obtained by sending the $A$ system through $\mathcal N$. Both maxima are attained.
--
--   This identifies the pure-state Holevo information (20.8) of Chapter 20 with Definition 13.3.1, and is the reason the converse bound $I(M;B^n)_\omega\le\chi(\mathcal N^{\otimes n})$ holds for codes whose codewords are mixed states.
--
--   **Formalization Note** The two maxima are `WildeQIT.HSW.holevoInfoMixed N.apply` and `WildeQIT.HSW.holevoInfo N.apply`, both written as suprema. The statement asserts their equality and exhibits a pure-state ensemble on which the supremum is attained; since a pure ensemble is also a mixed one, this gives attainment of both. The input space is assumed nonzero-dimensional, as all Hilbert spaces of the book are.
--
--   Differences from the source:
--   - encoding: max over input classical–quantum states on an arbitrary finite alphabet → sSup over alphabets {0,…,k−1} together with the existence of a maximizing pure ensemble; reason: mutual information is invariant under relabelling the alphabet, and attainment is stated explicitly
--   - encoding: Hilbert space H_A (nonzero, as throughout the book) → [Nonempty A]; reason: a zero-dimensional space carries no state, so no ensemble exists there
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 13.3.2, (13.104)–(13.105), p. 404; Definition 13.3.1, p. 401

import Mathlib
import Definitions.Def_WildeQIT_QChannel
import Definitions.Def_WildeQIT_FinDist
import Definitions.Def_WildeQIT_AFW_cqState
import Definitions.Def_WildeQIT_AFW_qMutualInfo
import Definitions.Def_WildeQIT_HSW_holevoInfo
import Definitions.Def_WildeQIT_HSW_holevoInfoMixed

open Matrix

namespace WildeQIT.HSW

/-- Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 13.3.2,
p. 404: "It is sufficient to maximize the Holevo information with respect to pure states:
χ(N) = max_{ρ_XA} I(X; B)_ρ = max_{τ_XA} I(X; B)_τ, (13.104) where
τ_XA ≡ Σ_x p_X(x)|x⟩⟨x|_X ⊗ |φ_x⟩⟨φ_x|_A, (13.105) and ρ_XB and τ_XB are the states that result
from sending the A system of ρ_XA and τ_XA through the quantum channel N_{A→B}, respectively."

**Formalization Note.** The maximum over mixed ensembles (Definition 13.3.1) is
`WildeQIT.HSW.holevoInfoMixed N.apply`, the one over pure ensembles (20.8) is
`WildeQIT.HSW.holevoInfo N.apply`; both are `sSup`s. The first conjunct is the equality of the
two; the second states that the pure-state supremum is a maximum, attained by some ensemble
`{p_X(x), |φ_x⟩}` (a pure ensemble is a mixed one, so the mixed maximum is attained too). The
input space is nonempty (`[Nonempty A]`), as is every Hilbert space of the book. -/
theorem theorem_13_3_2 {A B : Type} [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B]
    [DecidableEq B] (N : WildeQIT.QChannel A B) :
    holevoInfoMixed N.apply = holevoInfo N.apply ∧
      ∃ (k : ℕ) (p : WildeQIT.FinDist (Fin k)) (φ : Fin k → A → ℂ),
        (∀ x, star (φ x) ⬝ᵥ φ x = 1) ∧
        WildeQIT.AFW.qMutualInfo (WildeQIT.AFW.cqState (1 : Matrix (Fin k) (Fin k) ℂ) p
          (fun x => N.apply (Matrix.vecMulVec (φ x) (star (φ x))))) = holevoInfo N.apply := by sorry

end WildeQIT.HSW
