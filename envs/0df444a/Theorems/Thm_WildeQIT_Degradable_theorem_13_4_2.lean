-- Prove2me | Theorems.Thm_WildeQIT_Degradable_theorem_13_4_2
-- name    : WildeQIT.Degradable.theorem_13_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:56:51.266982+00:00
-- url     : https://prove2.me/theorems/dbee699f-3c21-47c8-8166-f94e3851b8fe
-- title:
--   Theorem 13.4.2 — the mutual information is concave in the input state
-- statement:
--   **Theorem 13.4.2.** Let $\mathcal N_{A'\to B}$ be a quantum channel, $p_X$ a probability distribution on a finite alphabet, and $\varphi^x_{AA'}$ pure states, one per letter, with a common reference system $A$. Let $\rho^x_{AB}\equiv\mathcal N_{A'\to B}(\varphi^x_{AA'})$, let $\sigma_{A'}\equiv\sum_x p_X(x)\rho^x_{A'}$ where $\rho^x_{A'}$ is the reduced state of $\varphi^x$ on $A'$, let $\varphi_{AA'}$ be a purification of $\sigma_{A'}$ and $\sigma_{AB}\equiv\mathcal N_{A'\to B}(\varphi_{AA'})$. Then
--
--   $$
--   \sum_x p_X(x)\,I(A;B)_{\rho^x}\le I(A;B)_\sigma .
--   $$
--
--   Since $I(A;B)_\sigma$ depends only on $\sigma_{A'}$, this says that the mutual information of a channel is a concave function of the input density operator, so $I(\mathcal N)$ can be computed by convex optimization.
--
--
--   **Formalization Note** Finite-dimensional systems are matrices over finite index types (the book's setting); entropies are the published von Neumann entropy `QAlgorithms.vnEntropy` in bits; bipartite systems are product index types in the Kronecker convention.
--
--   Differences from the source:
--   - encoding: a quantum channel N (linear, completely positive, trace-preserving map) → WildeQIT.QChannel, a finite Kraus family K_i with sum K_i^† K_i = I; reason: every finite-dimensional channel has such a Kraus form (Theorem 4.4.1); same instances
--   - encoding: φ_{AA′} is a purification of σ_{A′} (its purifying system unspecified) → φ is a unit vector on s × a, for an arbitrary finite index type s, with Tr_A |φ⟩⟨φ| = Σ_x p(x) Tr_A |φ^x⟩⟨φ^x|; reason: this is the definition of a purification; the purifying system is left as free as in the book, independent of the reference r of the states φ^x
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 13.4.2, eq. (13.137), p. 410

import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_WildeQIT_QChannel
import Definitions.Def_DattaDiscord_mutualInfo
import Definitions.Def_WildeQIT_partialTrace
import Definitions.Def_WildeQIT_FinDist

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 13.4.2, p. 410.
-/

namespace WildeQIT.Degradable

/-- **Theorem 13.4.2** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 410, eq. (13.137)). The mutual information `I(A; B)` is concave
in the input state: `∑ₓ p_X(x) I(A; B)_{ρˣ} ≤ I(A; B)_σ`, where
`ρˣ_{AB} ≡ N_{A′→B}(φˣ_{AA′})`, `σ_{A′} ≡ ∑ₓ p_X(x) ρˣ_{A′}`, `φ_{AA′}` is a purification
of `σ_{A′}`, and `σ_{AB} ≡ N_{A′→B}(φ_{AA′})`.

**Formalization Note.** `φˣ_{AA′}` are pure states (unit vectors) on `r × a`, with one reference
`A` of any finite dimension `r` shared by all `x`; the purification `φ_{AA′}` is a unit vector
on `s × a`, with its own reference of any finite dimension `s` (the book does not tie the
purifying system to the reference of the `φˣ`). `ρˣ_{A′} = Tr_A φˣ` is
`partialTraceLeft (pureDensity (φx x))`; "`φ` is a purification of `σ_{A′}`" is
`Tr_A |φ⟩⟨φ| = σ_{A′}`. `N_{A′→B}(·)` is `QAlgorithms.idTensorSuperop N.apply` and `I(A; B)` is
`DattaDiscord.mutualInfo`. `X` is any finite alphabet and `p` a probability distribution on it. -/
theorem theorem_13_4_2 {X r s a b : Type} [Fintype X] [Fintype r] [DecidableEq r] [Fintype s]
    [DecidableEq s] [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] (N : QChannel a b)
    (p : FinDist X) (φx : X → EuclideanSpace ℂ (r × a)) (hφx : ∀ x, ‖φx x‖ = 1)
    (φ : EuclideanSpace ℂ (s × a)) (hφ : ‖φ‖ = 1)
    (hpur : partialTraceLeft (QAlgorithms.pureDensity φ) =
      ∑ x, (p.prob x : ℂ) • partialTraceLeft (QAlgorithms.pureDensity (φx x))) :
    ∑ x, p.prob x * DattaDiscord.mutualInfo
        (QAlgorithms.idTensorSuperop (R := r) N.apply (QAlgorithms.pureDensity (φx x))) ≤
      DattaDiscord.mutualInfo
        (QAlgorithms.idTensorSuperop (R := s) N.apply (QAlgorithms.pureDensity φ)) := by sorry

end WildeQIT.Degradable
