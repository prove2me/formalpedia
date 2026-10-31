-- Prove2me | Theorems.Thm_TSPSDPGap_claim_4_15
-- name    : TSPSDPGap.claim_4_15
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:40:43.943283+00:00
-- url     : https://prove2.me/theorems/12bc4d19-28b1-486e-b5f8-1f64393be22a
-- title:
--   Claim 4.15 — $A$ and $B$ are simultaneously diagonalizable
-- statement:
--   Throughout, $g\ge2$ is even, $g\mid n$ and $g<n$ (the standing assumptions of §4), $d=n/2$, and $Y$ is the solution (3). For $k=0,\dots,n-1$ let $w_k=e^{-2\pi k\sqrt{-1}/n}$ and $v_k=(1,w_k,w_k^2,\dots,w_k^{n-1})\in\mathbb C^n$. Then
--
--   1. $Av_k=2a^{(k)}v_k$ and $Bv_k=2b^{(k)}v_k$ for every $k$;
--   2. $v_0,\dots,v_{n-1}$ are linearly independent, so they form a common eigenbasis of $A$ and $B$;
--   3. the eigenvalues of $A$ are exactly the numbers $2a^{(k)}$, and those of $B$ exactly the numbers $2b^{(k)}$, $k=0,\dots,n-1$.
--
--   Together with the Kronecker structure of (3) this gives the spectrum of $Y$ (Claim 4.18).
--
--   **Formalization Note** $A$ and $B$ are real; they act on the complex vectors $v_k$ after mapping their entries to $\mathbb C$. The eigenvalue sets are `spectrum ℝ`.
--
--   Differences from the source:
--   - reading: A and B are simultaneously diagonalizable, with λ_k(A), λ_k(B) for the same eigenvector v_k → A v_k = 2a^(k) v_k, B v_k = 2b^(k) v_k for all k, and the family (v_k) is linearly independent over ℂ; reason: n linearly independent common eigenvectors in ℂⁿ are a common eigenbasis, i.e. one invertible matrix diagonalizes both
--   - encoding: real matrices A, B with complex eigenvectors → A and B mapped entrywise to ℂ for the eigenvector equations; eigenvalue sets as spectrum ℝ of the real matrices; reason: Lean needs one scalar field per product; same eigenvalues
--   - encoding: standing assumptions of §4: g even, g groups of n/g vertices, a_i and b_i with denominators g, g − 1, n − g → hypotheses Even g, 2 ≤ g, g ∣ n, g < n; reason: the section's standing assumption (g even) plus the conditions under which (3) and a_i, b_i are defined; given g ∣ n they exclude only n/g ∉ ℕ, g ∈ {0, 1} and n − g = 0
--   - encoding: 1-based indices → 0-based Fin n indices; reason: Lean convention; same instances
-- source:
--   Gutekunst & Williamson, SDP Relaxations of the TSP and Their Integrality Gaps, arXiv:1907.09054v1, Claim 4.15, p.21 (eigenvectors as in Claim 3.8, p.10)

import Mathlib
import Definitions.Def_TSPSDPGap_Amat
import Definitions.Def_TSPSDPGap_Bmat
import Definitions.Def_TSPSDPGap_aHat
import Definitions.Def_TSPSDPGap_bHat

namespace TSPSDPGap

/-- **Claim 4.15: `A` and `B` are simultaneously diagonalizable, with eigenvalues `2a^(k)` and `2b^(k)`.**
Gutekunst & Williamson, *SDP Relaxations of the TSP and Their Integrality Gaps*,
arXiv:1907.09054v1, Claim 4.15, p.21:
"A and B are simultaneously diagonalizable. The eigenvalues of A are λ_k(A) = 2a^(k) for
k = 0, ..., n − 1. The eigenvalues of B are λ_k(B) = 2b^(k) for k = 0, ..., n − 1, where λ_k(A)
and λ_k(B) correspond to the same eigenvector v_k", with (p.21, and Claim 3.8, p.10)
`v_k = (1, w_k, w_k², …, w_k^{n−1})`, `w_k = e^{−2πk√−1/n}`.

**Standing hypotheses (§4, p.14).** `g` is even ("we thus assume that g is even throughout"),
`g ∣ n` ("g equally sized groups of n/g vertices"), `2 ≤ g` and `g < n` (the formulas for
`a_i, b_i` divide by `g − 1` and `n − g`; with `g ∣ n` they exclude only those undefined cases).

The statement: for every `k`, `A v_k = 2a^(k) v_k` and `B v_k = 2b^(k) v_k` (over `ℂ`); the
`v_k` are linearly independent (so they form a common eigenbasis); and the eigenvalues of `A`
and `B` are exactly `{2a^(k)}` and `{2b^(k)}`.

**Formalization Note.** `A = Amat g n`, `B = Bmat g n` (real matrices), mapped to `ℂ` for the
complex eigenvectors; `k : Fin n` (0-based); the eigenvalue sets are `spectrum ℝ`. -/
theorem claim_4_15 (g n : ℕ) (hg : Even g) (hg2 : 2 ≤ g) (hgn : g ∣ n) (hlt : g < n) :
    let w : Fin n → ℂ := fun k =>
      Complex.exp (-2 * (Real.pi : ℂ) * ((k : ℕ) : ℂ) * Complex.I / (n : ℂ))
    let v : Fin n → Fin n → ℂ := fun k u => w k ^ (u : ℕ)
    (∀ k : Fin n,
      ((Amat g n).map (fun x : ℝ => (x : ℂ))).mulVec (v k) = ((2 * aHat g n k : ℝ) : ℂ) • v k ∧
      ((Bmat g n).map (fun x : ℝ => (x : ℂ))).mulVec (v k) = ((2 * bHat g n k : ℝ) : ℂ) • v k) ∧
    LinearIndependent ℂ v ∧
    spectrum ℝ (Amat g n) = Set.range (fun k : Fin n => 2 * aHat g n k) ∧
    spectrum ℝ (Bmat g n) = Set.range (fun k : Fin n => 2 * bHat g n k) := by sorry

end TSPSDPGap
