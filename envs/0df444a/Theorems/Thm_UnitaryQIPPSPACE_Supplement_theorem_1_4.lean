-- Prove2me | Theorems.Thm_UnitaryQIPPSPACE_Supplement_theorem_1_4
-- name    : UnitaryQIPPSPACE.Supplement.theorem_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T16:38:46.989921+00:00
-- url     : https://prove2.me/theorems/1f41f2a8-8a04-4afe-9e2a-22514a53e97a
-- title:
--   Theorem 1.4 — $\mathsf{unitaryPSPACE}_{\varepsilon^4/2^{24}}\subseteq\mathsf{unitaryQIP}^{(\mathrm{poly})}_{0,1/2,\varepsilon}[3]$
-- statement:
--   Let $\varepsilon:\mathbb N\to(0,1/4]$ be polynomial-time computable with $1/\varepsilon$ polynomially bounded. Then
--   $$\mathsf{unitaryPSPACE}_{\varepsilon^4/2^{24}}\subseteq\mathsf{unitaryQIP}^{(\mathrm{poly})}_{0,1/2,\varepsilon}[3],$$
--   where in the notation $\mathsf{unitaryQIP}^{(m)}[\ell]$ the verifier receives $m(n)$ copies of the input state and acts in at most $\ell$ rounds during the interaction.
--
--   In words: every unitary family that a polynomial-space quantum computation implements to accuracy $\varepsilon(n)^4/2^{24}$ in trace distance (on every pure input) admits an interactive synthesis protocol with **three verifier rounds**, **perfect completeness** (an honest prover is accepted with probability $1$ on every input), soundness threshold $1/2$ and output error $\varepsilon(n)$, provided the time-uniform verifier receives polynomially many copies $|\psi\rangle^{\otimes m(n)}$ of the input. Together with Theorem 1.1 it shows that, in the multi-copy setting, unitary synthesis protocols can be compressed to three rounds.
--
--   **Formalization Note** The left side is the published class $\mathsf{unitaryPSPACE}_\delta$ at $\delta(n)=\varepsilon(n)^4/2^{24}$; the right side is the union over polynomially bounded copy numbers $m$ (chosen per family) of the multi-copy class with at most $3$ rounds, completeness error $0$ and threshold $1/2$.
--
--   Differences from the source:
--   - reading: ε : ℕ → (0, 1/4] polynomial-time computable → PolyTimeRat ε: rational values a/b (b ≥ 1) computed exactly from 1^n by a polynomial-time map; reason: the paper does not define computability of a real-valued function; the proof computes its parameters (r = ⌈2/(p0 ε²)⌉ etc.) from ε exactly ("All parameters and verifier circuits are computable in polynomial time"), which needs the value ε(n) itself
--   - reading: unitaryQIP^{(poly)} → unitaryQIPpoly: ∃ m with m(n) ≤ p(n) for a polynomial p, chosen after the family U; reason: Definition 2.11 and the gloss of the theorem; the proof chooses m = 2r with r depending on the family's round count k
--   - reading: [3]: the verifier acts in at most ℓ = 3 rounds → (V n).rounds.length ≤ 3 for every n; reason: the theorem's own gloss; rounds are counted as in the base verifier model (Lemma 5.1: "We construct the compressed verifier in three rounds"); verifiers below the threshold N are unconstrained otherwise, so "every n" adds nothing
--   - encoding: |ψ⟩^{⊗m(n)} → copiesVec n (m n) ψ on m(n)·n qubits, copy j on qubits j·n, …, j·n+n−1; reason: a fixed qubit layout of the tensor power; any other layout differs by a fixed qubit permutation the verifier can apply
--   - encoding: 1/ε polynomially bounded → ∃ q ∈ ℕ[X], ∀ n, 1/ε(n) ≤ q(n); reason: a real polynomial bound is dominated by a polynomial with natural coefficients, and since ε > 0 finitely many exceptions are absorbed into the constant term
-- source:
--   He, Ou, Zhao, unitaryQIP = unitaryPSPACE, arXiv:2611.02819 (held version, sha256 9e357a00…ead793), Theorem 1.4, p.4 (PDF p.6), restated p.38 (PDF p.40); proof pp.39–43 (PDF pp.41–45)

import Mathlib
import Definitions.Def_UnitaryQIPPSPACE_unitaryPSPACEd
import Definitions.Def_UnitaryQIPPSPACE_Supplement_unitaryQIPpoly
import Definitions.Def_UnitaryQIPPSPACE_Supplement_PolyTimeRat

namespace UnitaryQIPPSPACE

namespace Supplement

/-- **Theorem 1.4** (He, Ou, Zhao, *unitaryQIP = unitaryPSPACE*, arXiv:2611.02819, held version
sha256 9e357a00…, p. 4 (PDF p. 6), restated p. 38 (PDF p. 40)): "Let `ε : ℕ → (0, 1/4]` be
polynomial-time computable with `1/ε` polynomially bounded. Then,
`unitaryPSPACE_{ε⁴/2²⁴} ⊆ unitaryQIP^{(poly)}_{0,1/2,ε}[3]`, where in the notation
`unitaryQIP^{(m)}[ℓ]`, the verifier receives `m(n)` copies of the input state and acts in at most
`ℓ ∈ ℕ` rounds during the interaction."

**Formalization Note** "Polynomial-time computable" is `PolyTimeRat` (rational values computed
exactly from `1^n` in polynomial time); "`1/ε` polynomially bounded" is `1/ε(n) ≤ q(n)` for a
polynomial `q ∈ ℕ[X]` and every `n`. The left side is the published `unitaryPSPACEd` at
`δ(n) = ε(n)⁴/2²⁴`; the right side is `unitaryQIPpoly` with three rounds, completeness error
`0` and soundness threshold `1/2`, the copy number chosen per family. -/
theorem theorem_1_4 (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n ∧ ε n ≤ 1 / 4) (hcomp : PolyTimeRat ε)
    (hinv : ∃ q : Polynomial ℕ, ∀ n, 1 / ε n ≤ ((q.eval n : ℕ) : ℝ)) :
    unitaryPSPACEd (fun n => ε n ^ 4 / 2 ^ 24) ⊆
      unitaryQIPpoly 3 (fun _ => 0) (fun _ => 1 / 2) ε := by sorry

end Supplement

end UnitaryQIPPSPACE
