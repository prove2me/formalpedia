-- Prove2me | Theorems.Thm_SYKEdge_lemma_4_5
-- name    : SYKEdge.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:07:16.159863+00:00
-- url     : https://prove2.me/theorems/5776a2aa-517f-43cf-801d-9eaf8c6c239a
-- title:
--   Lemma 4.5 — $L(R)=\sum_{S,T}R_{S,T}a_S^*a_T$ is monotone in $R$ and $L(\mathrm{Id})=N$
-- statement:
--   For a Hermitian matrix $R\in\mathbb C^{\mathcal H\times\mathcal H}$ let $L(R)=\sum_{S,T\in\mathcal H}R_{S,T}\,a_S^*a_T$ on the twisted Fock space. Then
--
--   1. if $R\preceq R'$ (Loewner order) then $L(R)\preceq L(R')$, i.e. $\langle\psi,L(R)\psi\rangle\le\langle\psi,L(R')\psi\rangle$ for every $\psi\in\mathcal F$;
--   2. $L(\mathrm{Id})=N$.
--
--   This lets matrix inequalities for the sign matrix be lifted to operator inequalities on $\mathcal F$.
--
--   **Formalization Note** $R\preceq R'$ is "$R'-R$ is positive semidefinite"; the order on $\mathcal F$ compares real parts of expectation values.
--
--   Differences from the source:
--   - encoding: the §3 standing assumptions (n ⩾ k ⩾ 2 even, ℋ a k-uniform hypergraph) → IsKUniform n k m S: the same, with ℋ = (S_1, …, S_m) an indexed list and m ⩾ 1; reason: repeated hyperedges are distinct elements (footnote 6); m ⩾ 1 is needed for |ℋ|^{−1/2} and only excludes the empty hypergraph
--   - encoding: L ≼ L′ for ψ ∈ ⊕_{ℓ⩽t} F_ℓ, every t → fockLE: re⟨ψ, Lψ⟩ ⩽ re⟨ψ, L′ψ⟩ for every ψ ∈ F; reason: every element of F lies in some ⊕_{ℓ⩽t} F_ℓ; for Hermitian operators the expectation values are real
-- source:
--   Basu, Kothari, Midha, Sharp Bounds on Ground State Energy of the SYK Model, arXiv:2607.27185v2, Lemma 4.5 and the definitions of L(R) and ≼, p.22

import Mathlib
import Definitions.Def_SYKEdge_Fock
import Definitions.Def_SYKEdge_Hamiltonian
open Matrix ComplexOrder

namespace SYKEdge

/-- **Lemma 4.5** (Properties of `L`), A. Basu, P. K. Kothari, S. Midha, *Sharp Bounds on Ground State Energy of the SYK Model*,
arXiv:2607.27185v2, p.22.

For Hermitian `R, R' ∈ ℂ^{H×H}`: (1) if `R ≼ R'` then `L(R) ≼ L(R')`; (2) `L(Id) = N`, where
`L(R) := Σ_{S,T∈H} R_{S,T} a_S* a_T`.

**Formalization Note.** `R ≼ R'` is the Loewner order (`R' − R` positive semidefinite); `L ≼ L'` on `F`
is `fockLE` (`⟨ψ, Lψ⟩ ⩽ ⟨ψ, L'ψ⟩` for every `ψ ∈ F`, real parts). The hypergraph satisfies the §3
standing assumptions (`IsKUniform`). -/
theorem lemma_4_5 {n k m : ℕ} (S : Fin m → Finset (Fin n)) (hS : IsKUniform n k m S) :
    (∀ R R' : Matrix (Fin m) (Fin m) ℂ, R.IsHermitian → R'.IsHermitian → (R' - R).PosSemidef →
      fockLE (Lmap S R) (Lmap S R')) ∧
    Lmap S 1 = numTot m := by sorry

end SYKEdge
