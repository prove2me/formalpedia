-- Prove2me | Theorems.Thm_WildeQIT_AFW_condEntropy_abs_saturation
-- name    : WildeQIT.AFW.condEntropy_abs_saturation
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:36:23.336434+00:00
-- url     : https://prove2.me/theorems/66d27ddf-7fb2-4096-aca9-6a298aa7a74b
-- title:
--   Theorem 11.5.1 (saturation part): $H(A|B) = \log d_A$ at $\pi_A\otimes\sigma_B$ and $-\log d_A$ at $\Phi_{AB}$
-- statement:
--   This is the saturation clause of Theorem 11.5.1; the bound $|H(A|B)_\rho| \le \log\dim(\mathcal H_A)$ itself is the companion item `AlickiFannes.condEntropy_abs_le_log`.
--
--   Let $\mathcal H_A$ have dimension $d_A \ge 1$, and write $H(A|B)_\rho = H(AB)_\rho - H(B)_\rho$ for the conditional entropy (base-2 logarithms). Then:
--
--   1. for the maximally mixed state $\pi_A = I_A/d_A$ and every density operator $\sigma_B$ on $\mathcal H_B$,
--   $$
--   H(A|B)_{\pi_A\otimes\sigma_B} = \log d_A ;
--   $$
--   2. for the maximally entangled state $\Phi_{AB} = |\Phi\rangle\langle\Phi|_{AB}$, $|\Phi\rangle_{AB} = d_A^{-1/2}\sum_{i} |i\rangle_A|i\rangle_B$, on two systems of dimension $d_A$,
--   $$
--   H(A|B)_{\Phi} = -\log d_A .
--   $$
--
--   So the upper bound of (11.59) is attained by $\pi_A\otimes\sigma_B$ and the lower bound by $\Phi_{AB}$: the dimension bound on conditional entropy cannot be improved, and its use in the AFW inequality is tight in the dimension.
--
--   **Formalization Note** $H(A|B)$ is the published `AlickiFannes.condEntropy` (von Neumann entropy `QAlgorithms.vnEntropy`, base 2, tracing out the first factor). $\pi_A\otimes\sigma_B$ is the Kronecker product `(d_A⁻¹ • 1) ⊗ₖ σ` on `A × B`; $\Phi_{AB}$ is the matrix on `A × A` with entries $\delta_{ij}\delta_{kl}/d_A$ at $((i,j),(k,l))$. `A` is nonempty.
--
--   Differences from the source:
--   - reading: "the bounds are saturated" for $\pi_A\otimes\sigma_B$ and for $\Phi_{AB}$ → $H(A|B) = \log d_A$ at $\pi_A\otimes\sigma_B$ and $H(A|B) = -\log d_A$ at $\Phi_{AB}$; reason: the two bounds of $|H(A|B)| \le \log d_A$ are $H \le \log d_A$ and $H \ge -\log d_A$ (proof, (11.60)–(11.63)); the values say which state attains which, and give $|H(A|B)| = \log d_A$ in both cases.
--   - encoding: $\Phi_{AB}$ on $\mathcal H_A\otimes\mathcal H_B$ → $\Phi$ on `A × A`; reason: the maximally entangled state (3.232) is defined for $\dim\mathcal H_B = \dim\mathcal H_A$, so $\mathcal H_B$ is a copy of $\mathcal H_A$.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 11.5.1, p. 333 (saturation sentence after (11.59)); maximally entangled state (3.232), p. 114

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_AlickiFannes_condEntropy
import Definitions.Def_WildeQIT_IsDensityOperator

open scoped Kronecker

namespace WildeQIT.AFW

/-- Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 11.5.1, p. 333,
saturation clause: "The bounds are saturated for ρ_AB = π_A ⊗ σ_B, where π_A is the maximally mixed
state and σ_B ∈ D(H_B), and for ρ_AB = Φ_AB (the maximally entangled state)." The bound is
(11.59), `|H(A|B)_ρ| ≤ log dim(H_A)`, published as `AlickiFannes.condEntropy_abs_le_log`.

The two conjuncts give the values: `H(A|B) = log dim(H_A)` at `π_A ⊗ σ_B` (upper bound attained) and
`H(A|B) = −log dim(H_A)` at `Φ_AB` (lower bound attained).

**Formalization Note.** `H(A|B)` is the published `AlickiFannes.condEntropy` (base 2, traces out the
first factor). `π_A = I/dim(H_A)`; `σ_B` is any density operator (`WildeQIT.IsDensityOperator`).
`Φ_AB = |Φ⟩⟨Φ|` with `|Φ⟩ = d^{-1/2} Σ_i |i⟩_A|i⟩_B` ((3.232)) requires `dim(H_B) = dim(H_A)`, so
here `H_B` is a second copy of `A`, and `Φ_{(i,j),(k,l)} = δ_{ij} δ_{kl} / d`. `A` is nonempty
(`π_A` and `Φ_AB` need `dim(H_A) ≥ 1`). -/
theorem condEntropy_abs_saturation {A B : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] :
    (∀ σ : Matrix B B ℂ, WildeQIT.IsDensityOperator σ →
        AlickiFannes.condEntropy (((Fintype.card A : ℂ)⁻¹ • (1 : Matrix A A ℂ)) ⊗ₖ σ) =
          Real.logb 2 (Fintype.card A)) ∧
    AlickiFannes.condEntropy (Matrix.of fun (ij kl : A × A) =>
        if ij.1 = ij.2 ∧ kl.1 = kl.2 then (Fintype.card A : ℂ)⁻¹ else 0) =
      -Real.logb 2 (Fintype.card A) := by sorry

end WildeQIT.AFW
