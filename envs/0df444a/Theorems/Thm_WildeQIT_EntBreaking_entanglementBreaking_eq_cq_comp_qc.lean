-- Prove2me | Theorems.Thm_WildeQIT_EntBreaking_entanglementBreaking_eq_cq_comp_qc
-- name    : WildeQIT.EntBreaking.entanglementBreaking_eq_cq_comp_qc
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:27:42.251028+00:00
-- url     : https://prove2.me/theorems/93629c71-9cfa-472b-8261-dcdee10321cb
-- title:
--   Corollary 4.6.1 — every entanglement-breaking channel is a measurement followed by a preparation
-- statement:
--   Let $\mathcal N^{\mathrm{EB}}_{A\to B}$ be an entanglement-breaking channel between finite-dimensional Hilbert spaces. Then there are a finite classical system $Z$ with orthonormal basis $\{|z\rangle_Z\}$, a POVM $\{\Lambda^z_A\}$ on $A$ and density operators $\{\sigma^z_B\}$ on $B$ such that
--
--   $$
--   \mathcal N^{\mathrm{EB}}_{A\to B}=\mathcal P_{Z\to B}\circ\mathcal M_{A\to Z},
--   $$
--
--   where $\mathcal M_{A\to Z}(X)=\sum_z\operatorname{Tr}\{\Lambda^z_AX\}|z\rangle\langle z|_Z$ is a quantum–classical channel (4.288) and $\mathcal P_{Z\to B}(Y)=\sum_z\langle z|Y|z\rangle_Z\,\sigma^z_B$ is a classical–quantum channel (4.283). The equality is an equality of linear maps on all operators.
--
--   Every entanglement-breaking channel can thus be written as a measurement followed by a preparation.
--
--   **Formalization Note** $Z$ has the outcome set $\{0,\dots,m-1\}$ (`Fin m`) for some $m$, and both channels use its standard basis. The POVM condition is the published `FuchsVdGraaf.IsPOVM` (positive semidefinite operators summing to the identity), which is Definition 4.2.1 of the book.
--
--   Differences from the source:
--   - generalization: a quantum–classical channel $\mathcal M_{A\to Z}$ and a classical–quantum channel $\mathcal P_{Z\to B}$, each defined with some orthonormal basis of $\mathcal H_Z$ → both channels defined with the same basis, the standard basis of $Z$; reason: the Lean conclusion produces a more specific decomposition, which is in particular one of the book's (the book's proof, (4.314)–(4.315), uses one basis for both).
--   - encoding: a reference system of arbitrary size in "entanglement-breaking" → references $\mathbb C^r$ for every $r\in\mathbb N$; reason: every finite-dimensional reference is isomorphic to some $\mathbb C^r$.
--   - encoding: a classical system $Z$ with orthonormal basis $\{|z\rangle_Z\}$ → the outcome set $\{0,\dots,m-1\}$ (`Fin m`) for some $m$, with its standard basis; reason: every finite set is in bijection with some $\{0,\dots,m-1\}$.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Corollary 4.6.1, p. 169; Definitions 4.6.6–4.6.7, pp. 164–166

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_EntBreaking_IsQuantumChannel
import Definitions.Def_WildeQIT_EntBreaking_IsEntanglementBreaking
import Definitions.Def_FuchsVdGraaf_IsPOVM
import Definitions.Def_WildeQIT_EntBreaking_qcChannel
import Definitions.Def_WildeQIT_EntBreaking_cqChannel

namespace WildeQIT.EntBreaking

/-- **Corollary 4.6.1**, Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8,
p. 169: "An entanglement-breaking channel `N^EB_{A→B}` is a serial concatenation of a
quantum–classical channel `M_{A→Z}` with a classical–quantum channel `P_{Z→B}`, i.e.,
`N^EB_{A→B} = P_{Z→B} ∘ M_{A→Z}`. That is, every entanglement-breaking channel can be written as a
measurement followed by a preparation."

If `N` is an entanglement-breaking channel, there are a finite classical system `Z = ℂ^m`, a POVM
`{Λ_z}` on `A` (Definition 4.2.1, the published `FuchsVdGraaf.IsPOVM`) and density operators
`{σ_z}` on `B` such that `N = P ∘ M` as linear maps, where
`M(X) = ∑_z Tr{Λ_z X} |z⟩⟨z|_Z` is the quantum–classical channel (4.288) and
`P(Y) = ∑_z ⟨z|Y|z⟩ σ_z` is the classical–quantum channel (4.283).

**Formalization Note.** `Z` has the outcome set `Fin m` (every finite set is in bijection with
one) and its standard basis `{|z⟩}`, used by both channels, as in the book's proof ((4.314)–(4.315)). The equality is of linear maps on all of
`L(ℋ_A)`. -/
theorem entanglementBreaking_eq_cq_comp_qc {a b : Type} [Fintype a] [Fintype b]
    [DecidableEq a] (N : Matrix a a ℂ →ₗ[ℂ] Matrix b b ℂ)
    (hN : IsQuantumChannel N) (hEB : IsEntanglementBreaking N) :
    ∃ (m : ℕ) (Λ : Fin m → Matrix a a ℂ) (σ : Fin m → Matrix b b ℂ),
      FuchsVdGraaf.IsPOVM Λ ∧ (∀ z, WildeQIT.IsDensityOperator (σ z)) ∧
        N = (cqChannel σ).comp (qcChannel Λ) := by sorry

end WildeQIT.EntBreaking
