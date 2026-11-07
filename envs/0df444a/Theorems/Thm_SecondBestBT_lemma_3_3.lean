-- Prove2me | Theorems.Thm_SecondBestBT_lemma_3_3
-- name    : SecondBestBT.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:49:24.220626+00:00
-- url     : https://prove2.me/theorems/5d06f914-562f-4926-a15e-48ce15555079
-- title:
--   Lemma 3.3 — extension from a grid
-- statement:
--   Let $F_S,F_B$ be priors on $[0,1]$ and $M\in\mathbb N$. Let $\hat F^M_S,\hat F^M_B$ be the laws of the rounded values $\pi^M_S(s)$, $\pi^M_B(b)$, with masses $\hat f^M_S(k),\hat f^M_B(k)$ at $t_k=k2^{-M}$, $k=0,\dots,2^M$. Let $\hat x$ be a feasible grid allocation for these rounded priors: $\hat x\in[0,1]^{(2^M+1)^2}$, monotone grid interims, and $\Lambda^{\hat F^M_S,\hat F^M_B}_D(\hat x)\ge0$. Set
--   $$
--   x(s,b):=\hat x\big(\pi^M_S(s),\pi^M_B(b)\big).
--   $$
--   Then the interim allocations of $x$ are monotone on $[0,1]$ ($x_B$ weakly increasing, $x_S$ weakly decreasing),
--   $$
--   \Lambda^{F_S,F_B}_{\mathrm{gen}}(x)=\Lambda^{\hat F^M_S,\hat F^M_B}_D(\hat x),\qquad \mathrm{GFT}_{F_S,F_B}(x)\ge \mathrm{GFT}_{\hat F^M_S,\hat F^M_B}(\hat x),
--   $$
--   and hence $x$ is feasible: some payment rules make it a well-defined, BIC, interim-IR, ex-ante WBB mechanism with types in $[0,1]$, whose GFT is no smaller than that of $\hat x$.
--
--   The lemma is the step that gives $\mathrm{SB}(F_S,F_B)\ge\mathrm{SB}(\hat F^M_S,\hat F^M_B)$.
--
--   Differences from the source:
--   - encoding: $\hat x$ evaluated at the grid points $\pi^M_S(s)$, $\pi^M_B(b)$ → $\hat x$ indexed by grid indices: $x(s,b)=\hat x(\lceil 2^Ms\rceil,\lfloor 2^Mb\rfloor)$; reason: $\pi^M_S(s)=t_{\lceil 2^Ms\rceil}$ and $\pi^M_B(b)=t_{\lfloor 2^Mb\rfloor}$ on $[0,1]$
--   - encoding: "has a feasible extension" → there exist payment rules making $(x,p_B,p_S)$ a feasible mechanism with types in $[0,1]$; reason: the paper calls an allocation feasible when it satisfies the implementation conditions of Proposition 3.1
--   - encoding: mechanisms $(x,p_B,p_S)$ whose integrals are written without conditions → `WellDefined`: Borel measurable rules, $x\in[0,1]$ on $T\times T$, and finite interim-payment, budget-surplus and GFT integrals; reason: the paper's integrals presuppose these conditions; they only shrink the mechanism class, and the paper's constructions satisfy them
--   - encoding: independent priors $F_S,F_B$ supported on a set $A$ → probability measures on $\mathbb R$ with $\mu(\mathbb R\setminus A)=0$; independence is the product measure; reason: same objects
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Lemma 3.3, p.7

import Mathlib
import Definitions.Def_SecondBestBT_IsPriorOn
import Definitions.Def_SecondBestBT_secondBest
import Definitions.Def_SecondBestBT_lambdaGen
import Definitions.Def_SecondBestBT_IsGridFeasible
import Definitions.Def_SecondBestBT_gridGFT
import Definitions.Def_SecondBestBT_dyadicRoundS
import Definitions.Def_SecondBestBT_dyadicRoundB
import Definitions.Def_SecondBestBT_roundedMass

open MeasureTheory

namespace SecondBestBT

/-- **Lemma 3.3** (extension from a grid; Liu–Qin–Ren–Wang, *Second-Best Bilateral Trade is 1/2
Efficient*, arXiv:2606.03849, held version sha256 17184930…, Lemma 3.3, p.7). Let `μS`, `μB` be
priors on `[0, 1]`, `M ∈ ℕ`, and `F̂^M_S`, `F̂^M_B` the rounded priors with masses
`f̂^M_S(k)`, `f̂^M_B(k)` on the dyadic grid `t_k = k 2^{−M}`, `k = 0, …, 2^M`. Let `x̂` be a
feasible grid allocation for the rounded priors (the constraints of Corollary 3.2) and set
`x(s, b) := x̂(π^M_S(s), π^M_B(b))`. Then the interim allocations of `x` are monotone (`x_B`
weakly increasing, `x_S` weakly decreasing on `[0, 1]`),
`Λ_gen(x) = Λ^D_D(x̂)` (evaluated at the rounded priors) and `GFT(x) ≥ GFT_{F̂^M}(x̂)`. Hence `x`
is feasible: it is implemented by a BIC, interim-IR, ex-ante WBB mechanism with types in
`[0, 1]`, and its GFT is no smaller.

**Formalization Note** The grid matrix is indexed by grid indices, so
`x(s, b) = x̂(⌈2^M s⌉, ⌊2^M b⌋)`. The rounded masses are `f̂^M(k) = (μ.map π^M)({k 2^{−M}})`. -/
theorem lemma_3_3 (μS μB : Measure ℝ) (hS : IsPriorOn (Set.Icc 0 1) μS)
    (hB : IsPriorOn (Set.Icc 0 1) μB) (M : ℕ) (xh : ℕ → ℕ → ℝ)
    (hxh : IsGridFeasible (fun k => (k : ℝ) / 2 ^ M)
      (roundedMass (μS.map (dyadicRoundS M)) M) (roundedMass (μB.map (dyadicRoundB M)) M)
      (2 ^ M) xh) :
    MonotoneOn (interimB μS (fun p => xh ⌈(2 : ℝ) ^ M * p.1⌉₊ ⌊(2 : ℝ) ^ M * p.2⌋₊))
        (Set.Icc 0 1) ∧
      AntitoneOn (interimS μB (fun p => xh ⌈(2 : ℝ) ^ M * p.1⌉₊ ⌊(2 : ℝ) ^ M * p.2⌋₊))
        (Set.Icc 0 1) ∧
      lambdaGen μS μB (fun p => xh ⌈(2 : ℝ) ^ M * p.1⌉₊ ⌊(2 : ℝ) ^ M * p.2⌋₊) =
        lambdaDD (fun k => (k : ℝ) / 2 ^ M) (roundedMass (μS.map (dyadicRoundS M)) M)
          (roundedMass (μB.map (dyadicRoundB M)) M) (2 ^ M) xh ∧
      gridGFT (fun k => (k : ℝ) / 2 ^ M) (roundedMass (μS.map (dyadicRoundS M)) M)
          (roundedMass (μB.map (dyadicRoundB M)) M) (2 ^ M) xh ≤
        gft μS μB (fun p => xh ⌈(2 : ℝ) ^ M * p.1⌉₊ ⌊(2 : ℝ) ^ M * p.2⌋₊) ∧
      ∃ pB pS : ℝ × ℝ → ℝ, IsFeasible (Set.Icc 0 1) μS μB
        ⟨fun p => xh ⌈(2 : ℝ) ^ M * p.1⌉₊ ⌊(2 : ℝ) ^ M * p.2⌋₊, pB, pS⟩ := by sorry

end SecondBestBT
