-- Prove2me | Theorems.Thm_QBennettGill_lemma_10
-- name    : QBennettGill.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:11:27.959382+00:00
-- url     : https://prove2.me/theorems/c8bd7d5a-4963-4139-a4e5-d41496d7da40
-- title:
--   Lemma 10 — strong pre-image pseudorandomness of a random oracle
-- statement:
--   Let $p,q$ be polynomials and let $r=(r^{(n)})_n$ with $r^{(n)}\in\{0,1\}^{p(n)}$. Let $\mathcal A=(\mathcal A_n)_n$ be adversaries, where $\mathcal A_n$ receives a transcript $T$ and makes $q(n)$ quantum queries to $O_n:\{0,1\}^n\to\{0,1\}^n$; its initial state may encode arbitrary quantum advice. Then there is a negligible $\mathrm{negl}$ with, for all $n$,
--
--   $$\Big|\Pr\big[\mathcal A^{|O_n\rangle}(1^n,T)=1:O_n\leftarrow\mathcal O_n;\ T\leftarrow\mathcal D_0\big]-\Pr\big[\mathcal A^{|O_n\rangle}(1^n,T)=1:O_n\leftarrow\mathcal O_n;\ T\leftarrow\mathcal D_1\big]\Big|\le\mathrm{negl}(n),$$
--
--   where $\mathcal D_b=\mathcal D_b(n,O_n,p(n),r^{(n)})$ are the distributions of Box 1.
--
--   This is the paper's main technical lemma: a random oracle is a strong $(1-1/e)$-dense PRHF (Definition 6, item 3), which is what the zero-knowledge proof of the NIZK needs.
--
--   Differences from the source:
--   - generalization: for any non-uniform QPT oracle-aided adversary A → for every family of q(n)-query algorithms (q a polynomial) with arbitrary initial states (quantum advice) and arbitrary unitaries; reason: p.27: the proof works for any (potentially unbounded) A making polynomially many quantum queries; every non-uniform QPT adversary is such a family
--   - encoding: T = ({r_i}, {y_i}, {v_i}_{i∈I₀}); sampling from an empty set → T = (r, (y_i)_i, (v_i)_i) with v_i = 0ⁿ for i ∈ I₁; the empty set {0,1}ⁿ \ Image yields 0ⁿ; reason: a bijective re-encoding given r; 0ⁿ is the p.17 convention
--   - encoding: for any A, any polynomial p(n), any bit-vector r → ∀ p, ∀ A, ∀ r; reason: A's input type depends on p; an adversary for all lengths restricts to each p
-- source:
--   Liang, Yamakawa, Yung, Structured Quantum Hardness from Unstructured Assumptions, STOC 2027 submission (held manuscript, sha256 6464b75a…), Lemma 10, p.26 (PDF p.29); Box 1, p.25 (PDF p.28); p.27 (PDF p.30)

import Definitions.Def_QBennettGill_Negligible
import Definitions.Def_NoSignalPA_uniformExp
import Definitions.Def_QBennettGill_boxD0

set_option autoImplicit false

namespace QBennettGill

open BBBV.RandomOracle

/-- **Lemma 10** (strong pre-image pseudorandomness of a random oracle) for query-bounded adversaries:
for every polynomial `p`, every adversary family `A_n` (input a transcript `T`, `q(n)` quantum queries to
`O_n : {0,1}ⁿ → {0,1}ⁿ`, arbitrary initial state, so non-uniform with quantum advice) and every sequence of
bit-vectors `r = (r_1, …, r_{p(n)})`, there is a negligible `negl` with
`|Pr[A^{|O_n⟩}(1ⁿ, T) = 1 : O_n ← 𝒪_n; T ← D₀] − Pr[A^{|O_n⟩}(1ⁿ, T) = 1 : O_n ← 𝒪_n; T ← D₁]| ≤ negl(n)`,
with `D₀ = D₀(n, O_n, p(n), r)` and `D₁ = D₁(n, O_n, p(n), r)` of Box 1.

Liang, Yamakawa, Yung, *Structured Quantum Hardness from Unstructured Assumptions*,
STOC 2027 submission (held manuscript, sha256 6464b75a…), Lemma 10, p.26 (PDF p.29); p.27 (PDF p.30): "Our proof actually works for any (potentially
unbounded) A as long as she makes only a polynomial number of quantum oracle queries."

**Formalization Note.** Transcripts carry `r` and fill the hidden slots `i ∈ I₁` with `0ⁿ`. -/
theorem lemma_10 (p q : Polynomial ℕ) (W : ℕ → Type) [∀ n, Fintype (W n)] [∀ n, DecidableEq (W n)]
    (A : ∀ n : ℕ, Transcript n (p.eval n) → QueryAlg (Str n) (Str n) (W n) (q.eval n))
    (r : ∀ n : ℕ, Fin (p.eval n) → Bool) :
    ∃ negl : ℕ → ℝ, Negligible negl ∧ ∀ n : ℕ,
      |NoSignalPA.uniformExp (fun On : Str n → Str n =>
          ∑ T : Transcript n (p.eval n), boxD0 On (r n) T * acceptProb (A n T) (fun _ => On)) -
        NoSignalPA.uniformExp (fun On : Str n → Str n =>
          ∑ T : Transcript n (p.eval n), boxD1 On (r n) T * acceptProb (A n T) (fun _ => On))| ≤
        negl n := by sorry

end QBennettGill
