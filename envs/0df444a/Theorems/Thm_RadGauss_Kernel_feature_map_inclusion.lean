-- Prove2me | Theorems.Thm_RadGauss_Kernel_feature_map_inclusion
-- name    : RadGauss.Kernel.feature_map_inclusion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T16:28:10.460195+00:00
-- url     : https://prove2.me/theorems/eb226941-5e7b-4014-818d-fdcb96fc220b
-- title:
--   §4.3, p. 477 — ‖Σ α_iΦ(x_i)‖² = Σ α_iα_j k(x_i, x_j), hence F ⊆ {x ↦ ⟨w, Φ(x)⟩ : ‖w‖ ≤ B}
-- statement:
--   Let $k$ be a kernel on a compact space $\mathcal X$, and let $\Phi : \mathcal X \to \mathcal H$ be a feature map of $k$: $\mathcal H$ is a real Hilbert space with inner product $\langle \cdot, \cdot \rangle$ and norm $\|\cdot\|$, and $k(x_1, x_2) = \langle \Phi(x_1), \Phi(x_2) \rangle$ for all $x_1, x_2 \in \mathcal X$. Let $B \ge 0$ and let $F$ be the class of kernel expansions $x \mapsto \sum_{i=1}^m \alpha_i k(x, x_i)$ with $\sum_{i,j}\alpha_i\alpha_j k(x_i, x_j) \le B^2$. Then
--
--   1. for every $m$, all $x_1, \dots, x_m \in \mathcal X$ and all $\alpha_1, \dots, \alpha_m \in \mathbb R$,
--   $$\Big\|\sum_{i=1}^m \alpha_i \Phi(x_i)\Big\|^2 = \sum_{i,j} \alpha_i \alpha_j\, k(x_i, x_j);$$
--   2. consequently
--   $$F \subseteq \{\, x \mapsto \langle w, \Phi(x) \rangle \;:\; w \in \mathcal H,\ \|w\| \le B \,\}.$$
--
--   The inclusion places the kernel class inside a ball of linear functionals of the feature map, which is how its complexity is bounded in Lemma 22.
--
--   **Formalization Note** The feature map is a hypothesis (any real Hilbert space $\mathcal H$ and any $\Phi$ with $k = \langle\Phi(\cdot), \Phi(\cdot)\rangle$); its existence for every kernel is the cited RKHS theorem, available on the platform as `FoundationsML.Kernels.RKHS_exists`. The paper takes $B > 0$; here $B \ge 0$ (for $B < 0$ the right-hand set is empty while $F$ contains the zero function, so a sign condition is needed).
-- source:
--   Bartlett, Mendelson, Rademacher and Gaussian Complexities: Risk Bounds and Structural Results, J. Mach. Learn. Res. 3 (2002), p. 477 (PDF p. 15), §4.3, first and second displays

import Mathlib
import Definitions.Def_RadGauss_Kernel_KernelClass

namespace RadGauss.Kernel

/-- §4.3, p. 477 (Bartlett–Mendelson 2002), the feature-map displays. Let `k` be a kernel on `𝒳`
with feature map `Φ : 𝒳 → ℋ` into a real Hilbert space, `k(x₁, x₂) = ⟨Φ(x₁), Φ(x₂)⟩`. Then
`‖Σ_i α_i Φ(x_i)‖² = Σ_{i,j} α_i α_j k(x_i, x_j)` for every finite family, and hence, for `B ≥ 0`,
`F ⊆ {x ↦ ⟨w, Φ(x)⟩ : ‖w‖ ≤ B}`. The paper takes `B > 0`; `0 ≤ B` is assumed here. -/
theorem feature_map_inclusion {X H : Type*} [TopologicalSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (k : X → X → ℝ) (hk : IsKernel k) (Φ : X → H)
    (hΦ : ∀ x₁ x₂, k x₁ x₂ = inner ℝ (Φ x₁) (Φ x₂)) (B : ℝ) (hB : 0 ≤ B) :
    (∀ (m : ℕ) (x : Fin m → X) (α : Fin m → ℝ),
        ‖∑ i, α i • Φ (x i)‖ ^ 2 = ∑ i, ∑ j, α i * α j * k (x i) (x j)) ∧
      kernelClass k B ⊆ {f | ∃ w : H, ‖w‖ ≤ B ∧ f = fun x => inner ℝ w (Φ x)} := by sorry

end RadGauss.Kernel
