-- Prove2me | Theorems.Thm_SteurerHDX_lemma_2_1
-- name    : SteurerHDX.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:33:02.378179+00:00
-- url     : https://prove2.me/theorems/bd2cb6a7-b5fb-4efe-a257-49361db2e323
-- title:
--   Lemma 2.1: Rayleigh quotient characterization of $\lambda_2(P)$
-- statement:
--   This is the variational (Courant–Fischer) characterization of the second eigenvalue of a reversible random walk.
--
--   Let $W$ be the weighted adjacency matrix of a graph on a finite set with at least two points: $W$ symmetric, entrywise nonnegative, with all degrees $D(x)=\sum_yW(x,y)>0$. Let $P=D^{-1}W$ and let $\mu$ be its stationary distribution. Then
--   $$\lambda_2(P)=1-\min_{f\ne0,\ \langle f,\mathbf 1\rangle_\mu=0}\frac{\mathcal E_P(f,f)}{\langle f,f\rangle_\mu}=1-\min_{f\text{ non-constant}}\frac{\mathcal E_P(f,f)}{\mathrm{Var}_\mu(f)},$$
--   and both minima are attained.
--
--   Combined with a test function this gives upper bounds on the spectral gap; this is how Theorem 3.1 turns the gap hypothesis into the separation bound.
--
--   **Formalization Note** $\lambda_2$ is the second largest eigenvalue counted with multiplicity. Both minima are stated as least elements of the sets of quotients. $\mathcal E_P$ is the published Dirichlet form `GibbsCongestion.dirichletForm` $\tfrac12\sum_{x,y}\pi(x)P(x,y)(f(x)-f(y))(g(x)-g(y))$ evaluated at $P=D^{-1}W$ and $\pi=\mu$.
--
--   Differences from the source:
--   - encoding: a weighted graph G = (V, E, w) with P = D⁻¹A → a symmetric entrywise nonnegative matrix W with positive row sums, on a finite type with at least two elements; reason: Section 2.1's setting: positive degrees make P = D⁻¹A defined, and a one-state chain has no second eigenvalue; self-loops are allowed as the down-up walk needs
--   - reading: min over f : ⟨f, 1⟩_μ = 0 → min over f ≠ 0 with ⟨f, 1⟩_μ = 0; reason: the quotient is undefined at f = 0
--   - reading: min over f ≠ 1 → min over non-constant f; reason: the quotient is undefined for every constant f (Var_μ(f) = 0), so f ≠ 1 means f not a multiple of 1
-- source:
--   Ebrahimnejad–Oveis Gharan, High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture, arXiv:2606.00292, Lemma 2.1, p.3

import Mathlib
import Definitions.Def_SteurerHDX_innerMu
import Definitions.Def_SteurerHDX_walk
import Definitions.Def_SteurerHDX_variance
import Definitions.Def_SteurerHDX_lambdaTwo
import Definitions.Def_GibbsCongestion_dirichletForm

namespace SteurerHDX

/-- **Lemma 2.1 (Rayleigh quotient).** Ebrahimnejad–Oveis Gharan, *High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture*, arXiv:2606.00292, Lemma 2.1, p.3: "The second eigenvalue of P is
λ₂(P) = 1 − min_{f:⟨f,1⟩_μ=0} E_P(f, f)/⟨f, f⟩_μ = 1 − min_{f≠1} E_P(f, f)/Var_μ(f)."

**Formalization Note.** The setting is Section 2.1: a weighted graph, given by a symmetric,
entrywise nonnegative weight matrix `W` with positive degrees (self-loops allowed), P = D⁻¹W,
μ stationary. λ₂ is counted with multiplicity (`lambdaTwo`). E_P(f, g) is the published
`GibbsCongestion.dirichletForm P π f g = ½ ∑_x ∑_y π(x) P(x,y)(f(x) − f(y))(g(x) − g(y))` with
P = `walk W` = D⁻¹W and π = `statDist W` = μ, which is the page's ½ E_{x∼μ} ∑_y P(x,y)(…)(…). Both minima are attained
(`IsLeast`). In the first, f ranges over nonzero f with ⟨f, 1⟩_μ = 0 (the quotient is undefined
at 0); in the second, "f ≠ 1" is read as f non-constant (the quotient is undefined for
constants). At least two states are assumed (a one-state chain has no second eigenvalue). -/
theorem lemma_2_1 {ι : Type*} [Fintype ι] (W : Matrix ι ι ℝ) (hcard : 2 ≤ Fintype.card ι)
    (hsymm : ∀ x y, W x y = W y x) (hnn : ∀ x y, 0 ≤ W x y) (hdeg : ∀ x, 0 < vdeg W x) :
    IsLeast {c : ℝ | ∃ f : ι → ℝ, f ≠ 0 ∧ innerMu W f (fun _ => 1) = 0 ∧
        c = GibbsCongestion.dirichletForm (walk W) (statDist W) f f / innerMu W f f} (1 - lambdaTwo W) ∧
      IsLeast {c : ℝ | ∃ f : ι → ℝ, (∃ x y, f x ≠ f y) ∧
        c = GibbsCongestion.dirichletForm (walk W) (statDist W) f f / variance W f} (1 - lambdaTwo W) := by sorry

end SteurerHDX
