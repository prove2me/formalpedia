-- Prove2me | Theorems.Thm_WildeQIT_EntBreaking_adjoint_completelyPositive_unital
-- name    : WildeQIT.EntBreaking.adjoint_completelyPositive_unital
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:27:17.593522+00:00
-- url     : https://prove2.me/theorems/e3babb00-0fb2-480b-816c-21e588c9a956
-- title:
--   Proposition 4.4.1 — the adjoint of a quantum channel is completely positive and unital
-- statement:
--   Let $\mathcal N:\mathcal L(\mathcal H_A)\to\mathcal L(\mathcal H_B)$ be a quantum channel (linear, completely positive, trace preserving) between finite-dimensional Hilbert spaces, and let $\mathcal N^\dagger:\mathcal L(\mathcal H_B)\to\mathcal L(\mathcal H_A)$ be its adjoint, the linear map with $\operatorname{Tr}\{Y^\dagger\mathcal N(X)\}=\operatorname{Tr}\{\mathcal N^\dagger(Y)^\dagger X\}$ for all $X,Y$. Then
--
--   1. $\mathcal N^\dagger$ is completely positive, and
--   2. $\mathcal N^\dagger$ is unital:
--   $$
--   \mathcal N^\dagger(I_B)=I_A .
--   $$
--
--   The adjoint is the Heisenberg-picture form of the channel: it maps a POVM $\{\Lambda^j_B\}$ on the output to the POVM $\{\mathcal N^\dagger(\Lambda^j_B)\}$ on the input.
--
--   **Formalization Note** The statement holds for every linear map satisfying the adjoint equations (4.235); such a map is unique.
--
--   Differences from the source:
--   - encoding: the adjoint $\mathcal N^\dagger$ → any linear map satisfying the defining equations (4.235); reason: the adjoint is the unique such map (Definition 4.4.6), and one exists in finite dimension.
--   - encoding: complete positivity with a reference of arbitrary size → references $\mathbb C^r$ for every $r\in\mathbb N$; reason: every finite-dimensional reference is isomorphic to some $\mathbb C^r$.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Proposition 4.4.1, p. 158; Definitions 4.4.6–4.4.7, p. 157

import Mathlib
import Definitions.Def_WildeQIT_EntBreaking_IsQuantumChannel
import Definitions.Def_WildeQIT_EntBreaking_IsAdjointMap

namespace WildeQIT.EntBreaking

/-- **Proposition 4.4.1**, Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8,
p. 158: "The adjoint `N† : L(ℋ_B) → L(ℋ_A)` of a quantum channel `N : L(ℋ_A) → L(ℋ_B)` is a
completely positive, unital map."

If `N` is a quantum channel and `Nadj` is its adjoint (Definition 4.4.6: the linear map with
`Tr{Y† N(X)} = Tr{N†(Y)† X}` for all `X`, `Y`), then `Nadj` is completely positive
(Definition 4.4.2) and unital, `Nadj(I_B) = I_A` (Definition 4.4.7, p. 157).

**Formalization Note.** The adjoint is unique, so quantifying over every linear `Nadj` satisfying
the defining equations (4.235) is a statement about `N†`. Complete positivity is
`QAlgorithms.Entanglement.IsCompletelyPositive` (reference as the first factor, every finite
size). -/
theorem adjoint_completelyPositive_unital {a b : Type} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b]
    (N : Matrix a a ℂ →ₗ[ℂ] Matrix b b ℂ) (Nadj : Matrix b b ℂ →ₗ[ℂ] Matrix a a ℂ)
    (hN : IsQuantumChannel N) (hadj : IsAdjointMap N Nadj) :
    QAlgorithms.Entanglement.IsCompletelyPositive Nadj ∧ Nadj 1 = 1 := by sorry

end WildeQIT.EntBreaking
