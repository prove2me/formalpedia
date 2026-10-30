-- Prove2me | Theorems.Thm_ShorEBAdditivity_eq_12
-- name    : ShorEBAdditivity.eq_12
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:17:54.265441+00:00
-- url     : https://prove2.me/theorems/128726d3-743f-42af-a963-037dcadcd3b7
-- title:
--   Eq. (12): chain rule $H(\sum_j q_j\gamma_j\otimes|j\rangle\langle j|) - \sum_j H(q_j|j\rangle\langle j|) = \sum_j q_jH(\gamma_j)$
-- statement:
--   Let $q_1,\dots,q_m \ge 0$ and let $\gamma_1,\dots,\gamma_m$ be density matrices on a common finite-dimensional space. Let $\{|j\rangle\}$ be the standard basis of $\mathbb C^m$. Then
--
--   $$
--   H\Big(\sum_j q_j\,\gamma_j\otimes|j\rangle\langle j|\Big) - \sum_j H\big(q_j\,|j\rangle\langle j|\big) = \sum_j q_j\, H(\gamma_j),
--   $$
--
--   where $H(X) = -\operatorname{Tr} X\log X$ is the von Neumann entropy functional, so that $H(q_j|j\rangle\langle j|) = -q_j\log q_j$.
--
--   This chain rule for block-diagonal (classical–quantum) states is what turns the conditional entropy $H(\sigma_{ABC}) - H(\sigma_{BC})$ into the average output entropy $\sum_j q_j H(\Psi(|a_j\rangle\langle a_j|))$ in (11) and (23).
--
--   **Formalization Note** $H$ is `QAlgorithms.vnEntropy`, in bits, applied literally to the unnormalized matrices $q_j|j\rangle\langle j|$. The flag register is the second tensor factor, indexed by `Fin m`. The weights need not sum to one.
--
--   Differences from the source:
--   - reading: γ_j and q_j unspecified in (12) → γ_j density matrices and q_j ≥ 0; reason: in (11) the rule is applied to the states Ψ(|a_j⟩⟨a_j|) with the weights q_j of (18); the identity is false for γ_j of trace ≠ 1
--   - encoding: H(ρ) = −Tr ρ log ρ, base unspecified → vnEntropy in bits (log₂); reason: both sides scale by the same factor under a change of base
--   - encoding: |j⟩ an orthonormal set (the flag register C) → the standard basis vectors of ℂ^m, |j⟩⟨j| = Matrix.single j j 1 on Fin m; reason: entropy is invariant under the unitary taking one orthonormal set to another; same values
-- source:
--   Shor, Additivity of the Classical Capacity of Entanglement-Breaking Quantum Channels, arXiv:quant-ph/0201149v3, eq. (12), p.3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Ensemble

open QAlgorithms
open scoped Kronecker

namespace ShorEBAdditivity

/-- Shor, *Additivity of the Classical Capacity of Entanglement-Breaking Quantum Channels*,
arXiv:quant-ph/0201149v3, eq. (12), p.3: "The second equality follows from the chain rule for
entropy, namely H(Σ_j qj γj ⊗ |j⟩⟨j|) − Σ_j H(qj |j⟩⟨j|) = Σ_j qj H(γj)."

For nonnegative numbers `q_j` and density matrices `γ_j` on a common finite space, with `|j⟩` an
orthonormal flag basis,
`H(Σ_j q_j γ_j ⊗ |j⟩⟨j|) − Σ_j H(q_j |j⟩⟨j|) = Σ_j q_j H(γ_j)`.

**Formalization Note.** `H` is `QAlgorithms.vnEntropy` (bits, `0 log 0 = 0`). The terms
`H(q_j |j⟩⟨j|)` are taken literally: the entropy functional of the unnormalized matrix
`q_j |j⟩⟨j|`, which is `−q_j log₂ q_j`. The `γ_j` are density matrices (the paper applies the
rule to the states `Ψ(|a_j⟩⟨a_j|)`); the weights need not sum to one, as on the page. The flag
register is `Fin m`, the second Kronecker factor. -/
theorem eq_12 {G : Type*} [Fintype G] [DecidableEq G] {m : ℕ} (q : Fin m → ℝ)
    (hq : ∀ j, 0 ≤ q j) (γ : Fin m → Matrix G G ℂ) (hγ : ∀ j, IsDensityMatrix (γ j)) :
    vnEntropy (∑ j, (q j : ℂ) • (γ j ⊗ₖ Matrix.single j j (1 : ℂ))) -
        ∑ j, vnEntropy ((q j : ℂ) • Matrix.single j j (1 : ℂ)) =
      ∑ j, q j * vnEntropy (γ j) := by sorry

end ShorEBAdditivity
