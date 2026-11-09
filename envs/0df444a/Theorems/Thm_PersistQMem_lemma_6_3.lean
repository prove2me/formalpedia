-- Prove2me | Theorems.Thm_PersistQMem_lemma_6_3
-- name    : PersistQMem.lemma_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:48:21.876325+00:00
-- url     : https://prove2.me/theorems/19d20d7d-6e2a-4888-a93e-5b6efc7d6b46
-- title:
--   Lemma 6.3 — Kraus source bound: $\sum_jp_j\|c_j\|_\sigma^2\le\zeta(K)$ and $\sum_jp_jb_j\le B_K$
-- statement:
--   Let the data of Definition 2.1 be fixed, let the entering memory be $\mathbb C^r$ with $r\le K$, and let $\Phi$ be a complete refined instrument whose output blocks have dimension $k_a\le K$. For every unit entering memory vector $u$,
--   $$\sum_jp_j\|c_j\|_\sigma^2\le\zeta(K),\qquad\sum_jp_jb_j\le B_K.\tag{37}$$
--
--   This is where the memory bound $K$ enters: each record's effective Kraus operator has rank at most $K$, so it is a feasible point of the profile $\zeta(K)$.
--
--   Differences from the source:
--   - encoding: H_σ, the quotient of Hermitian recorded tests by zero-variance tests → the range of the isometric real-linear map π X = ⊕_a (X_a − Tr(σX) I) L_a in real coordinates (Hsig); maps on tests are transported through a fixed linear section; reason: π is isometric for ⟨·,·⟩_σ and its kernel is the zero-variance tests, so its range is the quotient; maps that vanish on zero-variance tests do not depend on the section
--   - encoding: ‖c_j‖²_σ → the squared norm of c_j in H_σ; reason: H_σ carries the σ-inner product
--   - encoding: unit vector u ∈ C^r → u : Fin r → ℂ with star u ⬝ᵥ u = 1; reason: Lean convention; same vectors
-- source:
--   Tao, Shen, Structural Lower Bounds for Quantum Property Estimation with Persistent Memory, STOC 2027 submission (manuscript of 2026-11-03, sha256 6d48ad24…), Lemma 6.3, (37), p.22 (PDF p.25); §6.2, p.19 (r ≤ K)

import Mathlib
import Definitions.Def_PersistQMem_Hsig

open scoped Matrix ComplexOrder InnerProductSpace

namespace PersistQMem

/-- **Lemma 6.3 (Kraus source bound), p.22** (Tao, Shen, *Structural Lower Bounds for Quantum
Property Estimation with Persistent Memory*, STOC 2027 submission, manuscript of 2026-11-03,
sha256 6d48ad24…, Lemma 6.3, p.22). For the complete refined instrument `Φ` (output blocks
`k_a ≤ K`, entering memory `C^r` with `r ≤ K`, §6.2 p.19) and any unit entering memory vector `u`,
(37) `Σ_j p_j ‖c_j‖²_σ ≤ ζ(K)` and `Σ_j p_j b_j ≤ B_K`. -/
theorem lemma_6_3 {D M : ℕ} {G : Fin M → Matrix (Fin D) (Fin D) ℂ} {p : Fin M → ℝ}
    (hG : ProfileData G p) {ι : Type} [Fintype ι] {r K : ℕ} (hrK : r ≤ K)
    (Φ : FinInstrument ι r D K) (u : Fin r → ℂ) (hu : star u ⬝ᵥ u = 1) :
    ∑ j, p j * ‖cvec Φ u (G j)‖ ^ 2 ≤ profile G p K ∧
    ∑ j, p j * bcoef Φ u (G j) ≤ budget G p K := by sorry

end PersistQMem
