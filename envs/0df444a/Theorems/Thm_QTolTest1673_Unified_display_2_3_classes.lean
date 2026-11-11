-- Prove2me | Theorems.Thm_QTolTest1673_Unified_display_2_3_classes
-- name    : QTolTest1673.Unified.display_2_3_classes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:21:51.270795+00:00
-- url     : https://prove2.me/theorems/28eb22cb-3920-4b77-82ff-0034919934f4
-- title:
--   §2.3 display (p. 15) — $L_{n,k}$ and $J_{n,k}$ as unions of block-constant classes
-- statement:
--   For a subspace $V\le\mathbb F_2^n$ let $C_V$ be the Boolean functions constant on every coset $x+V^\perp$, let $V_T=\{u:\operatorname{supp}(u)\subseteq T\}$ for $T\subseteq[n]$, and let $\mathcal V_k^{\dim}$ (subspaces of dimension at most $k$) and $\mathcal V_k^{\mathrm{junta}}$ (the $V_T$ with $|T|\le k$) be the candidate families. For all $n$ and $k$,
--   $$L_{n,k}=\bigcup_{V\in\mathcal V_k^{\dim}}C_V,\qquad J_{n,k}=\bigcup_{V\in\mathcal V_k^{\mathrm{junta}}}C_V,$$
--   where $L_{n,k}=\{x\mapsto h(Ax)\}$ with $A\in\mathbb F_2^{k\times n}$ and $J_{n,k}$ is the class of $k$-juntas.
--
--   This reduces both testing problems to the same question about a family of subspaces: is $f$ close to some block-constant class $C_V$ with $V$ in the candidate family?
--
--   Differences from the source:
--   - encoding: $f:\mathbb F_2^n\to\{\pm1\}$ → its bit function `BoolFn n` with $f=(-1)^{b_f}$ (`toSign`); reason: a bijection; the XOR oracle adds $b_f=(1-f)/2$; same instances
--   - encoding: coordinates $[n]=\{1,\dots,n\}$ → `Fin n` = $\{0,\dots,n-1\}$; reason: index base only; same instances
--   - encoding: $\operatorname{supp}(u)=\{i:u_i=1\}\subseteq T$ → $u_i\ne0\Rightarrow i\in T$; reason: over $\mathbb F_2$, $u_i\ne0$ iff $u_i=1$
-- source:
--   Zekun Ye, Jialin Zhang, Quantum Tolerant Testing of Fourier Dimensionality and Juntas, STOC 2027 submission #1673 (October 2026), source.pdf SHA-256 5f8e9058de57e5bfe86cd485966905d576e77df38d613213662f8930b3e0e51e, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1673.pdf, §2.3, display on p. 15

import Definitions.Def_QTolTest1673_Unified_Classes

namespace QTolTest1673.Unified

open FourierDimTesting102.Quantum

/-- §2.3 display, p. 15: `L_{n,k} = ⋃_{V ∈ V_k^dim} C_V` and `J_{n,k} = ⋃_{V ∈ V_k^junta} C_V`,
where `C_V` is the class of Boolean functions constant on every coset `x + V^⊥`. -/
theorem display_2_3_classes (n k : ℕ) :
    linJunta n k = ⋃ W ∈ famDim n k, blockConst W ∧
      junta n k = ⋃ W ∈ famJunta n k, blockConst W := by sorry

end QTolTest1673.Unified
