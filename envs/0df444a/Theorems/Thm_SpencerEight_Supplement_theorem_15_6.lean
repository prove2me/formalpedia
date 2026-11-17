-- Prove2me | Theorems.Thm_SpencerEight_Supplement_theorem_15_6
-- name    : SpencerEight.Supplement.theorem_15_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T23:53:38.155204+00:00
-- url     : https://prove2.me/theorems/3839d492-cdb8-42b5-ab21-6673da1169b4
-- title:
--   Theorem 15.6 — the explicit family $\mathcal B_k=\{P_{x,x^3+x}\}$ has every signing of norm at least $\sqrt{2n}$, so $D^{\mathrm{mat}}_n\ge\sqrt2\sqrt n$ for $n=2^k$
-- statement:
--   Let $k\ge1$ and $n=d=2^k$. For $u,v\in\mathbb F_2^k$ let $P_{u,v}\in\mathbb R^{2^k\times2^k}$ have entries $(P_{u,v})_{y,y\oplus u}=(-1)^{v\cdot y}$ and $0$ elsewhere. Identify $\mathbb F_2^k$ with $\mathrm{GF}(2^k)$ through a self-dual basis and put $\mathcal B_k:=\{P_{x,x^3+x}:x\in\mathrm{GF}(2^k)\}$. Then:
--
--   1. a self-dual basis of $\mathrm{GF}(2^k)$ over $\mathbb F_2$ exists;
--   2. for every self-dual basis, $\mathcal B_k$ consists of $2^k$ distinct real symmetric signed permutation matrices squaring to $I_{2^k}$;
--   3. for every self-dual basis and every signing $\varepsilon\in\{-1,1\}^{\mathrm{GF}(2^k)}$, with $S:=\sum_x\varepsilon_xP_{x,x^3+x}$,
--   $$
--   \mathrm{tr}[S^2]=n^2,\qquad\frac1n\,\mathrm{tr}[S^4]=2n^2,\qquad\|S\|\ge\sqrt{2n}=1.414213\ldots\times\sqrt n;
--   $$
--   4. in particular $D^{\mathrm{mat}}_n\ge\sqrt2\,\sqrt n$.
--
--   This is an explicit family at every power of two, with no existence argument: its fourth-moment identity holds at every signing and forces the norm bound.
--
--   **Formalization Note** $\mathrm{GF}(2^k)$ is `GaloisField 2 k` (with a `Fintype` instance taken as a binder; all instances agree), $\mathrm{Tr}$ is `Algebra.trace`, and $\mathbb F_2^k$ is `Fin k → ZMod 2`, which indexes the rows and columns of $P_{u,v}$. "$2^k$ distinct matrices" is stated as $|\mathrm{GF}(2^k)|=2^k$ together with injectivity of $x\mapsto P_{x,x^3+x}$. $\mathrm{tr}$ is the matrix trace.
--
--   Differences from the source:
--   - generalization: the existence of a self-dual basis is shown in Step 1 of the proof (p.292), not stated in the theorem → the conclusion asserts that a self-dual basis exists; reason: the theorem presupposes one ("so the theorem is non-vacuous"); the added clause only strengthens the statement, and the remaining clauses are the source's
--   - reading: identify F₂^k with GF(2^k) through a self-dual basis → the clauses hold for every self-dual basis b; reason: the source fixes an arbitrary self-dual basis and its proof works for each; the universal reading is the stronger one
--   - encoding: the trace Tr[x] = x + x² + ⋯ + x^{2^{k−1}} → Algebra.trace (ZMod 2) (GaloisField 2 k); reason: for a finite field the algebra trace is the sum of the Galois conjugates; same function
--   - encoding: B_k consists of 2^k distinct matrices → Fintype.card (GaloisField 2 k) = 2^k ∧ Function.Injective (familyB b); reason: same content for an indexed family
--   - encoding: ‖S‖ ≥ √(2n) = 1.414213… × √n → √(2n) ≤ ‖S‖, √(2n) = √2·√n, 1.414213 ≤ √2 < 1.414214; reason: the truncated-decimal convention of p.288
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Theorem 15.6, p.291 (PDF p.291); self-dual basis existence, Step 1, p.292

import Mathlib
import Definitions.Def_SpencerEight_signedSum
import Definitions.Def_SpencerEight_Supplement_IsSignedPerm
import Definitions.Def_SpencerEight_Supplement_IsSelfDualBasis
import Definitions.Def_SpencerEight_Supplement_familyB
import Definitions.Def_SpencerEight_Supplement_Dmat
open scoped Matrix.Norms.L2Operator

namespace SpencerEight.Supplement

/-- Theorem 15.6 (An explicit family at constant `√2` for every `n = 2^k`), Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), p.291
(PDF p.291). Let `k ≥ 1` and `n = d = 2^k`. For every self-dual basis `b` of `GF(2^k)` over `F₂`, the
family `B_k = {P_{x, x³+x} : x ∈ GF(2^k)}` (`familyB b`) consists of `2^k` distinct real symmetric signed
permutation matrices squaring to the identity, and for every signing `ε`, with `S := ∑ₓ εₓ P_{x,x³+x}`,
`tr[S²] = n²`, `(1/n) tr[S⁴] = 2n²` and `‖S‖ ≥ √(2n) = 1.414213… × √n`. Moreover `D^mat_n ≥ √2 √n`.

**Formalization Note** `GF(2^k)` is `GaloisField 2 k`, given a `Fintype` instance as a binder (all such
instances agree). "2^k distinct": the map `x ↦ P_{x,x³+x}` is injective and `|GF(2^k)| = 2^k`. The norm is
the L2 operator norm and `tr` the matrix trace. The conclusion also asserts that a self-dual basis exists,
which the source proves (Step 1) so that the theorem is not vacuous. `1.414213…` is a truncated decimal of
`√2`: `1.414213 ≤ √2 < 1.414214`. -/
theorem theorem_15_6 (k : ℕ) (hk : 1 ≤ k) [Fintype (GaloisField 2 k)] :
    (∃ b : Module.Basis (Fin k) (ZMod 2) (GaloisField 2 k), IsSelfDualBasis b) ∧
    (∀ b : Module.Basis (Fin k) (ZMod 2) (GaloisField 2 k), IsSelfDualBasis b →
      Fintype.card (GaloisField 2 k) = 2 ^ k ∧
      Function.Injective (familyB b) ∧
      (∀ x, (familyB b x).IsSymm ∧ IsSignedPerm (familyB b x) ∧ familyB b x * familyB b x = 1) ∧
      ∀ ε : GaloisField 2 k → ℝ, (∀ x, ε x = 1 ∨ ε x = -1) →
        Matrix.trace (signedSum (familyB b) ε ^ 2) = ((2 : ℝ) ^ k) ^ 2 ∧
        1 / (2 : ℝ) ^ k * Matrix.trace (signedSum (familyB b) ε ^ 4) = 2 * ((2 : ℝ) ^ k) ^ 2 ∧
        Real.sqrt (2 * (2 : ℝ) ^ k) ≤ ‖signedSum (familyB b) ε‖) ∧
    Real.sqrt (2 * (2 : ℝ) ^ k) = Real.sqrt 2 * Real.sqrt ((2 : ℝ) ^ k) ∧
    1.414213 ≤ Real.sqrt 2 ∧ Real.sqrt 2 < 1.414214 ∧
    Real.sqrt 2 * Real.sqrt ((2 : ℝ) ^ k) ≤ Dmat (2 ^ k) := by sorry

end SpencerEight.Supplement
