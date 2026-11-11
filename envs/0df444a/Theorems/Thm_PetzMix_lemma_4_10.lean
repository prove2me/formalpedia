-- Prove2me | Theorems.Thm_PetzMix_lemma_4_10
-- name    : PetzMix.lemma_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:15:54.442513+00:00
-- url     : https://prove2.me/theorems/2ec8aac8-34ed-4bd2-a218-fd68349d4ecb
-- title:
--   Lemma 4.10 — anchored increment estimate
-- statement:
--   Fix constants $C_F,\mu_F>0$ and $M$. There is a constant $C$, depending only on $M,C_F,\mu_F$, such that the following holds for every local dimension $d\ge1$. Let $B$ be a block, $\tau_B$ a full-rank state on $B$ satisfying Assumption 4.4 with constants $C_F,\mu_F$, and let $S=N_s(\partial B)$ be a boundary neighbourhood. Let $X,Y\in\mathcal A_S$ satisfy
--   $$
--   E_B(X^\dagger X)=E_B(Y^\dagger Y)=I,\qquad\|X\|,\|Y\|\le M .
--   $$
--   Then every Hermitian $A$ satisfies
--   $$
--   \big\|E_B\big(X^\dagger AX-Y^\dagger AY\big)\big\|\le C\,(|S|+1)\,\|X-Y\|\,\|A\|_L .
--   $$
--
--   The cost is linear in the size of the boundary neighbourhood rather than in the block length; this is what makes the shell increments summable.
--
--   **Formalization Note** $C$ is chosen before $d$, $n$, the block, $\tau_B$ and $s$; the proof gives $C=\max(2M,4MC_F/(1-e^{-\mu_F}))$.
--
--   Differences from the source:
--   - generalization: a fixed finite local dimension d → every d ≥ 1; reason: d = 1 is the trivial one-dimensional site; every d of the paper is included
--   - reading: 'there is a constant C' → ∃ C chosen before d, n, the block, τ_B, S, X, Y (C depends only on M, C_F, µ_F); reason: the proof gives C = max(2M, 4MC_F/(1 − e^{−µ_F})) ((87), (94)), with no dimension factor (p.24), and the constant is used uniformly over blocks in Corollary 4.11
--   - encoding: the periodic chain Λn = ℤ/nℤ and operators on regions → sites Fin n, operators QDSGibbs.Op, region operators as A ⊗ I (SupportedOn); reason: Lean convention; same instances
--   - encoding: a block B = [a, b] ⊊ Λn → cycBlock ℓ a with 1 ≤ ℓ < n; reason: a nonempty proper cyclic interval is exactly such a block
--   - encoding: a full-rank state τ_B on B → T = τ_B ⊗ I_{B^c} with IsBlockRef B T (positive definite, trivial on B^c, ptr B T = 1); reason: the same objects, re-embedded on the full chain
--   - encoding: 'Suppose that Assumption … holds' with 'there exist constants' → the per-block predicates Asm43/Asm44 with their constants quantified before n, h and the block; reason: output constants independent of n and B, as the paper states
-- source:
--   Kim, Rapid mixing of quantum spin chains at any finite temperature, arXiv:2610.01190 (held copy sha256 38ff48d0…), Lemma 4.10, (84)–(85), p.25; S = N_s(∂B), p.24; Assumption 4.4, (61)–(62), p.20

import Mathlib
import Definitions.Def_PetzMix_HasExtInfluence
import Definitions.Def_PetzMix_petzAmp

open scoped Matrix ComplexOrder ENNReal

set_option autoImplicit false

namespace PetzMix

open QDSGibbs

/-- **Lemma 4.10 (Anchored increment estimate)** (Kim, Rapid mixing of quantum spin chains at any finite temperature, arXiv:2610.01190 (held copy sha256 38ff48d0…), Lemma 4.10, (84)–(85), p.25; `S = N_s(∂B)`
fixed on p.24). Suppose Assumption 4.4 holds. Let `X, Y ∈ A_S` satisfy `E_B(X†X) = E_B(Y†Y) = I` and
`‖X‖, ‖Y‖ ≤ M`. Then there is a constant `C` such that every Hermitian `A` satisfies
`‖E_B(X†AX − Y†AY)‖ ≤ C (|S| + 1) ‖X − Y‖ ‖A‖_L`.

**Formalization Note** `C` depends only on `M`, `C_F`, `µ_F` (it is chosen before `d`, `n`, the
block and `τ_B`; the proof gives `C = max(2M, 4MC_F/(1 − e^{−µ_F}))`, (87), (94), with no dimension
factor, p.24). The block is `B = cycBlock ℓ a`, `1 ≤ ℓ < n`, `τ_B` any full-rank state on `B`
(`IsBlockRef B T`), `S = nbhd s (bdry B)` and `|S|` its cardinality. Assumption 4.4 is the per-block
predicate `Asm44`. -/
theorem lemma_4_10 (CF μF : ℝ) (hCF : 0 < CF) (hμF : 0 < μF) (M : ℝ) :
    ∃ C : ℝ, ∀ (d : ℕ), 1 ≤ d → ∀ (n : ℕ) (a : Fin n) (ℓ : ℕ), 1 ≤ ℓ → ℓ < n →
      ∀ T : ChainOp n d, IsBlockRef (cycBlock ℓ a) T → Asm44 a ℓ T CF μF →
      ∀ (s : ℕ) (X Y : ChainOp n d),
        SupportedOn (nbhd s (bdry (cycBlock ℓ a))) X →
        SupportedOn (nbhd s (bdry (cycBlock ℓ a))) Y →
        condExp (cycBlock ℓ a) T (Xᴴ * X) = 1 → condExp (cycBlock ℓ a) T (Yᴴ * Y) = 1 →
        opNorm X ≤ M → opNorm Y ≤ M →
        ∀ A : ChainOp n d, A.IsHermitian →
          opNorm (condExp (cycBlock ℓ a) T (Xᴴ * A * X - Yᴴ * A * Y)) ≤
            C * (((nbhd s (bdry (cycBlock ℓ a))).card : ℝ) + 1) * opNorm (X - Y) * lip A := by sorry

end PetzMix
