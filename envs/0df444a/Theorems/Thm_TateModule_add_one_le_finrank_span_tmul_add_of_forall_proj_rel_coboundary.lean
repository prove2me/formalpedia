-- Prove2me | Theorems.Thm_TateModule_add_one_le_finrank_span_tmul_add_of_forall_proj_rel_coboundary
-- name    : TateModule.add_one_le_finrank_span_tmul_add_of_forall_proj_rel_coboundary
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/02fceabb-10de-50dc-8a50-7ee23abb06f6
-- title:
--   Rank bound for Tate vectors with coboundary relations
-- statement:
--   Fix a prime $\ell$ and an additive abelian group $J$, and let $T_\ell(J)$ denote the group of sequences $x:\mathbb{N}\to J$ with $\ell^k\,x_k=0$ and $\ell\,x_{k+1}=x_k$ for all $k$, with $\mathrm{proj}_k$ the evaluation $x\mapsto x_k$. Let $n,m$ be natural numbers with $n>0$, and let $\mathrm{src},\mathrm{tgt}:\{0,\dots,m-1\}\to\{0,\dots,n-1\}$ be arbitrary maps (the end maps of a graph with $m$ edges and $n$ vertices). Let $\kappa$ be a field together with a sequence $\zeta:\mathbb{N}\to\kappa$ satisfying $\zeta_0=1$, $\zeta_{k+1}^{\ell}=\zeta_k$ for all $k$, and $\zeta_1\neq 1$. Let $x_0,\dots,x_{m-1}\in T_\ell(J)$, and assume: for every level $k$ and every integer vector $(c_e)_e$ with $\sum_e c_e\,\mathrm{proj}_k(x_e)=0$ in $J$, there exists $b:\{0,\dots,n-1\}\to\kappa$ with all $b_i\neq 0$ and $\zeta_k^{c_e}\,b_{\mathrm{src}(e)}=b_{\mathrm{tgt}(e)}$ for every $e$. Assume finally that $\mathbb{Q}_\ell\otimes_{\mathbb{Z}_\ell}T_\ell(J)$ is finite-dimensional over $\mathbb{Q}_\ell$. Then $m+1\le d+n$, where $d$ is the $\mathbb{Q}_\ell$-dimension of the span of the vectors $1\otimes x_e$ in $\mathbb{Q}_\ell\otimes_{\mathbb{Z}_\ell}T_\ell(J)$.
--
--   A purely algebraic rank bound: the hypothesis says that all integral relations among the $x_e$ become, at each finite level, coboundaries for the graph with end maps $\mathrm{src},\mathrm{tgt}$, and the conclusion bounds the corank of the span by the cycle rank $m-n+1$ of that graph. It is the final step in the proof of independence of Kummer-type classes attached to a semistable covering, used there to produce enough independent vectors in the rational Tate module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateModule_add_one_le_finrank_span_tmul_add_of_forall_proj_rel_coboundary.lean

import Definitions.Def_ModularCurve_JZeroTateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem TateModule.add_one_le_finrank_span_tmul_add_of_forall_proj_rel_coboundary
    (ℓ : ℕ) [Fact ℓ.Prime] (J : Type) [AddCommGroup J]
    (n m : ℕ) (hn : 0 < n) (src tgt : Fin m → Fin n)
    (κ : Type) [Field κ] (ζ : ℕ → κ) (hζ0 : ζ 0 = 1) (hζ : ∀ k, ζ (k + 1) ^ ℓ = ζ k) (hζ1 : ζ 1 ≠ 1)
    (x : Fin m → TateModule ℓ J)
    (H : ∀ (k : ℕ) (c : Fin m → ℤ), (∑ e, c e • TateModule.proj ℓ J k (x e)) = 0 →
      ∃ b : Fin n → κ, (∀ i, b i ≠ 0) ∧ ∀ e, ζ k ^ (c e) * b (src e) = b (tgt e))
    [FiniteDimensional ℚ_[ℓ] (ModularCurve.RationalTateModule ℓ J)]
    :
    m + 1 ≤ Module.finrank ℚ_[ℓ] ↥(Submodule.span ℚ_[ℓ]
      (Set.range fun e : Fin m => ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x e : ModularCurve.RationalTateModule ℓ J))) + n := by sorry
