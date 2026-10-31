-- Prove2me | Theorems.Thm_RobustToDynamics_theorem_2_7
-- name    : RobustToDynamics.theorem_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:41:32.368028+00:00
-- url     : https://prove2.me/theorems/2e5e276b-e233-416b-94ad-15f0506b663b
-- title:
--   Theorem 2.7 — $\mathcal S=\mathcal S_r$ for an $r$ computable in time polynomial in $\sigma(A,b,G)$, and R-LD-LPs with $\rho(G)\le\rho^*<1$ are solvable in polynomial time
-- statement:
--   Let $\sigma(A,b,G)$ denote the size of the rational data $A\in\mathbb Q^{m\times n}$, $b\in\mathbb Q^m$, $G\in\mathbb Q^{n\times n}$, let $P=\{x\in\mathbb R^n: Ax\le b\}$, and let
--   $$
--   \mathcal S=\bigcap_{k=0}^{\infty}\{x: AG^kx\le b\},\qquad \mathcal S_r=\bigcap_{k=0}^{r}\{x: AG^kx\le b\}
--   $$
--   as in (2.3) and (2.6).
--
--   1. There is an algorithm that, given $(A,b,G)$, computes a nonnegative integer $r$ (output in binary) in time polynomial in $\sigma(A,b,G)$ such that, whenever $\rho(G)<1$, $P$ is bounded and the origin is in the interior of $P$,
--   $$
--   \mathcal S=\mathcal S_r .
--   $$
--   2. For every fixed rational $\rho^*<1$ there is an algorithm that, given $(A,b,c,G)$, runs in time polynomial in their size and, whenever $\rho(G)\le\rho^*$, $P$ is bounded and the origin is in the interior of $P$, outputs an optimal solution $x\in\mathbb Q^n$ of the R-LD-LP
--   $$
--   \min\{c^Tx : G^kx\in P\ \text{for } k=0,1,2,\dots\}. \tag{2.2}
--   $$
--
--   This is the main result of §2.1: under $\rho(G)<1$ the infinitely many constraints of an R-LD-LP reduce to finitely many, with a step count that is computable in polynomial time, and the problem is polynomial-time solvable when $\rho(G)$ is bounded away from $1$.
--
--   **Formalization Note** Complexity is read in the standard Turing model (footnote 3, p.5) as Mathlib's `Turing.TM2ComputableInPolyTime` over the four-letter alphabet `OnlineCRS.Combine.Sym` (bits $0,1$; $2$ separates numerator and denominator; $3$ separates items). Numbers are written in binary with the published encodings `encNat`, `encRat` (lowest terms) and `encVec`, so the length of an encoding is polynomially related to the size $\sigma$ of p.13. The output of the first algorithm is $r$ in binary; the output of the second is the list of the $n$ coordinates of $x$. Both algorithms must halt in polynomial time on every input; their outputs are constrained only under the hypotheses.
--
--   Differences from the source:
--   - encoding: computable in time polynomial in the size σ (standard Turing model) → Nonempty (Turing.TM2ComputableInPolyTime ea eb f) with binary encodings over Fin 4; reason: Mathlib's Turing-machine model; the encodings write every number in binary (rationals in lowest terms) with dimensions first, so their length is polynomially related to σ
--   - encoding: r computed in time polynomial in σ(A, b, G) → f : LDData → ℕ with output encNat (binary); reason: r is bounded only pseudo-polynomially (p.17, footnote 9), so it is output in binary as the source's polynomial-time claim requires
--   - encoding: the algorithm is run on instances satisfying the hypotheses → a total function computed in polynomial time on every encoded input, constrained only under the hypotheses; reason: a polynomial-time machine must halt on every input; constraining its output only on the instances the source speaks about changes no instance
--   - reading: R-LD-LPs with ρ(G) ≤ ρ* can be solved → the algorithm outputs a rational optimal solution of (2.2), as a list of n rationals; reason: the proof (p.16) optimizes cᵀx over S_r = S, which returns an optimal solution; under the hypotheses one exists (0 ∈ S, S compact)
--   - reading: the second claim (Furthermore, …) without restating the If-clause → the second claim keeps P bounded and 0 ∈ int P; reason: its proof (p.16) uses (2.15) and (2.16), which need both, and the summary on p.17 says "under the assumptions of Theorem 2.7"
--   - encoding: time polynomial in σ(A, b, c, G, ρ*) for a fixed ρ* → ∀ ρ* : ℚ, ρ* < 1 → ∃ a polynomial-time machine (its polynomial may depend on ρ*); reason: ρ* is fixed, so σ(ρ*) is a constant; ρ* is not part of the input (footnote 7)
--   - encoding: ρ(G) = max of |λ| over the (real or complex) eigenvalues → specRadius, the supremum of |z| over the complex spectrum; reason: the complex spectrum of an n × n matrix is finite and nonempty for n ≥ 1, so the supremum is the maximum; same value
-- source:
--   Ahmadi & Günlük, Robust-to-Dynamics Optimization, arXiv:1805.03682v2, Theorem 2.7, pp.13–14

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_RobustToDynamics_specRadius
import Definitions.Def_RobustToDynamics_polyhedron
import Definitions.Def_RobustToDynamics_feasibleSet
import Definitions.Def_RobustToDynamics_outerApprox
import Definitions.Def_RobustToDynamics_IsMinimizer
import Definitions.Def_RobustToDynamics_LDData
import Definitions.Def_RobustToDynamics_encLD
import Definitions.Def_RobustToDynamics_RLDLP
import Definitions.Def_RobustToDynamics_encRLD
import Definitions.Def_RobustToDynamics_encListRat

open Matrix

namespace RobustToDynamics

/-- **Theorem 2.7: `S = S_r` for a polynomial-time computable `r`, and R-LD-LPs with
`ρ(G) ≤ ρ* < 1` are solvable in polynomial time.**
Ahmadi & Günlük, *Robust-to-Dynamics Optimization*, arXiv:1805.03682v2, Theorem 2.7, pp.13–14:
"Let σ(A, b, G) denote the size of A, b, and G. Let S and Sr be as in (2.3) and (2.6) respectively.
If ρ(G) < 1, P = {x ∈ Rn| Ax ≤ b} is bounded, and the origin is in the interior of P, then S = Sr
for some nonnegative integer r that can be computed in time polynomial in σ(A, b, G). Furthermore,
for any fixed rational number ρ∗ < 1, R-LD-LPs with ρ(G) ≤ ρ∗ can be solved in time polynomial in
σ(A, b, c, G, ρ∗)."

(a) There is a function `f` from rational data `(A, b, G)` to natural numbers, computable by a
Turing machine in time polynomial in the length of the binary encoding of `(A, b, G)` (output in
binary), such that `S = S_{f(A,b,G)}` whenever `ρ(G) < 1`, `P` is bounded and `0 ∈ int P`.

(b) For every rational `ρ* < 1` there is a function `g` from rational R-LD-LP instances
`(A, b, c, G)` to lists of rationals, computable by a Turing machine in time polynomial in the
length of the encoding of `(A, b, c, G)`, such that whenever `ρ(G) ≤ ρ*`, `P` is bounded and
`0 ∈ int P`, `g(A, b, c, G)` has `n` entries and is an optimal solution of
`min {cᵀx : Gᵏx ∈ P for k = 0, 1, 2, …}` (2.2).

**Formalization Note.** `ℝⁿ` is `Fin n → ℝ`, with the rational data cast to `ℝ`; `ρ(G)` is
`specRadius` (complex spectrum). Polynomial time is Mathlib's `Turing.TM2ComputableInPolyTime` over
`OnlineCRS.Combine.Sym = Fin 4`: inputs are `encLD` / `encRLD` (dimensions, then the entries in
binary, rationals in lowest terms), whose length is polynomially related to the size σ of p.13;
the output of (a) is `encNat` (binary) and the output of (b) is `encListRat`. The machines halt in
polynomial time on every input; their outputs are constrained only under the hypotheses. In (b)
the polynomial may depend on the fixed `ρ*`, which is not part of the input, and the hypotheses
"P bounded" and "0 ∈ int P" of the theorem's If-clause are kept. -/
theorem theorem_2_7 :
    (∃ f : LDData → ℕ,
      Nonempty (Turing.TM2ComputableInPolyTime encLD OnlineCRS.Combine.encNat f) ∧
      ∀ d : LDData,
        specRadius (d.G.map (Rat.cast : ℚ → ℝ)) < 1 →
        Bornology.IsBounded (polyhedron (d.A.map (Rat.cast : ℚ → ℝ)) (fun i => (d.b i : ℝ))) →
        (0 : Fin d.n → ℝ) ∈
          interior (polyhedron (d.A.map (Rat.cast : ℚ → ℝ)) (fun i => (d.b i : ℝ))) →
        feasibleSet (d.A.map (Rat.cast : ℚ → ℝ)) (fun i => (d.b i : ℝ))
            (d.G.map (Rat.cast : ℚ → ℝ)) =
          outerApprox (d.A.map (Rat.cast : ℚ → ℝ)) (fun i => (d.b i : ℝ))
            (d.G.map (Rat.cast : ℚ → ℝ)) (f d)) ∧
    (∀ ρstar : ℚ, ρstar < 1 →
      ∃ g : RLDLP → List ℚ,
        Nonempty (Turing.TM2ComputableInPolyTime encRLD encListRat g) ∧
        ∀ I : RLDLP,
          specRadius (I.data.G.map (Rat.cast : ℚ → ℝ)) ≤ (ρstar : ℝ) →
          Bornology.IsBounded
            (polyhedron (I.data.A.map (Rat.cast : ℚ → ℝ)) (fun i => (I.data.b i : ℝ))) →
          (0 : Fin I.data.n → ℝ) ∈
            interior (polyhedron (I.data.A.map (Rat.cast : ℚ → ℝ)) (fun i => (I.data.b i : ℝ))) →
          (g I).length = I.data.n ∧
            IsMinimizer (fun j => (I.c j : ℝ))
              (feasibleSet (I.data.A.map (Rat.cast : ℚ → ℝ)) (fun i => (I.data.b i : ℝ))
                (I.data.G.map (Rat.cast : ℚ → ℝ)))
              (fun j : Fin I.data.n => (((g I).getD j 0 : ℚ) : ℝ))) := by sorry

end RobustToDynamics
