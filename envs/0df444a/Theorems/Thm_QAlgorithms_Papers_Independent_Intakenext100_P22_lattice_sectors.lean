-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P22_lattice_sectors
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P22.lattice_sectors
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:49:21.966213+00:00
-- url     : https://prove2.me/theorems/acff33a4-0703-4344-a38f-2419b912fce8
-- title:
--   Theta lattice minima, domain-wall sectors, and amplitudes
-- statement:
--   Fix $n\ge2$. For $v\in\mathbb R^{n-1}$ set $v_0=v_n=0$, $C^{(k)}_{rs}=\cos(2\pi k(r-s)/n)$, and $f_y=2\gamma_E+\psi(y)+\psi(1-y)$, where $\psi$ is the digamma function. Define
--   $$a(v)=\frac2n\sum_{k=1}^{n-1}\sin^2(\pi k/n)\,v^tC^{(k)}v,\quad
--   b(v)=\frac2n\sum_{k=1}^{n-1}\sin^2(\pi k/n)f_{k/n}\,v^tC^{(k)}v.$$
--   Then for every real vector,
--   $$a(v)=\frac12\sum_{j=0}^{n-1}(v_{j+1}-v_j)^2.$$
--   For $0\le a<b\le n-1$ and $s\in\{-1,1\}$ let $B_{a,b,s}$ equal $s$ on $a<j\le b$ and zero elsewhere. Every nonzero integer vector has $a(v)\ge1$, with equality exactly for these blocks; moreover,
--   $$b(B_{a,b,s})=-2\log[2n\sin(\pi(b-a)/n)],\qquad
--   B_{a,b,s}^tC^{(k)}B_{a,b,s}=\frac{\sin^2(\pi k(b-a)/n)}{\sin^2(\pi k/n)}\quad(1\le k<n).$$
--   Over $v=m+\varepsilon$, with $m\in\mathbb Z^{n-1}$ and nonzero $\varepsilon\in\{0,1/2\}^{n-1}$, the minimum is $1/4$. Equality holds exactly when $v=B_{a,b,s}/2$, and $b(B_{a,b,s}/2)=b(B_{a,b,s})/4$.
--
--   The integer vectors with $a(v)=2$ are exactly the following patterns, for $0\le a<b<c<d\le n-1$ and $s=\pm1$:
--   $$M_0=B_{a,b,s}+B_{c,d,s},\quad M_1=B_{a,b,s}-B_{c,d,s},\quad M_2=B_{a,d,s}+B_{b,c,s}.$$
--   Write $s_{uv}=\sin(\pi(v-u)/n)$ and
--   $$Q_0=\frac{s_{bd}s_{ac}}{s_{ab}s_{cd}s_{ad}s_{bc}},\quad
--   Q_1=\frac{s_{ad}s_{bc}}{s_{ab}s_{cd}s_{bd}s_{ac}},\quad
--   Q_2=\frac{s_{ab}s_{cd}}{s_{bd}s_{ac}s_{ad}s_{bc}}.$$
--   Their amplitudes are
--   $$b(M_r)=\log\!\left[\left(\frac{Q_r}{4n^2}\right)^2\right],\qquad r=0,1,2.$$
--   These second-sector patterns require $n\ge4$. For $n=2$ and $n=3$, the smallest energy strictly above $1$ is respectively $4$ and $3$, and each value is attained. These classifications determine the first theta-lattice contributions independently of any physical moment formula.
-- source:
--   Entanglement entropy of two disjoint intervals in conformal field theory II, arXiv:1011.5482v1, PDF p. 14, §5.1, §5.3, §5.4, equations (59)–(66), (75)–(77), (85), (90)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P22

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P22

open scoped BigOperators Topology

open Filter MeasureTheory

/-- PDF pp. 14–18, (59)–(66),(75)–(77),(85),(90): Fourier/chain identity,
all integer and half-characteristic minimizers, second-sector patterns and
amplitudes. Both signs and exceptional n=2,3 next energies are retained.
In (90) the logarithm is of the square, not the square of the logarithm. -/
theorem lattice_sectors (n : ℕ) (hn : 2 ≤ n) :
    (∀ v : Fin (n - 1) → ℝ, exponentA n v = chainEnergy n v) ∧
    (∀ m : Fin (n - 1) → ℤ, m ≠ 0 →
      1 ≤ exponentA n (fun i => (m i : ℝ)) ∧
      (exponentA n (fun i => (m i : ℝ)) = 1 ↔
        ∃ a b : ℕ, ∃ s : ℝ, a < b ∧ b ≤ n - 1 ∧ (s = 1 ∨ s = -1) ∧
          (fun i => (m i : ℝ)) = intervalBlock n a b s)) ∧
    (∀ a b : ℕ, ∀ s : ℝ, a < b → b ≤ n - 1 → (s = 1 ∨ s = -1) →
      exponentA n (intervalBlock n a b s) = 1 ∧
      exponentB n (intervalBlock n a b s) = -2 * Real.log (2 * n * sheetSine n a b)) ∧
    (∀ a b k : ℕ, ∀ s : ℝ, a < b → b ≤ n - 1 →
      1 ≤ k → k < n → (s = 1 ∨ s = -1) →
      cosineQuadratic n k (intervalBlock n a b s) =
        (Real.sin (Real.pi * (k : ℝ) / n * ((b : ℝ) - a)) /
          Real.sin (Real.pi * (k : ℝ) / n)) ^ 2) ∧
    (∀ e : Fin (n - 1) → Bool, ∀ m : Fin (n - 1) → ℤ,
      e ≠ (fun _ => false) →
      1 / 4 ≤ exponentA n (halfShift n e m) ∧
      (exponentA n (halfShift n e m) = 1 / 4 ↔
        ∃ a b : ℕ, ∃ s : ℝ, a < b ∧ b ≤ n - 1 ∧ (s = 1 ∨ s = -1) ∧
          halfShift n e m = intervalBlock n a b (s / 2))) ∧
    (∀ a b : ℕ, ∀ s : ℝ, a < b → b ≤ n - 1 → (s = 1 ∨ s = -1) →
      exponentA n (intervalBlock n a b (s / 2)) = 1 / 4 ∧
      exponentB n (intervalBlock n a b (s / 2)) = exponentB n (intervalBlock n a b s) / 4) ∧
    (∀ m : Fin (n - 1) → ℤ,
      exponentA n (fun i => (m i : ℝ)) = 2 ↔
        ∃ a b c d : ℕ, ∃ s : ℝ, ∃ r : Fin 3,
          a < b ∧ b < c ∧ c < d ∧ d ≤ n - 1 ∧ (s = 1 ∨ s = -1) ∧
          (fun i => (m i : ℝ)) = secondPattern n a b c d s r) ∧
    (∀ a b c d : ℕ, ∀ s : ℝ, ∀ r : Fin 3,
      a < b → b < c → c < d → d ≤ n - 1 → (s = 1 ∨ s = -1) →
      exponentB n (secondPattern n a b c d s r) =
        Real.log ((qFactor n a b c d r / (4 * (n : ℝ) ^ 2)) ^ 2)) ∧
    (n = 2 →
      (∀ m : Fin (n - 1) → ℤ, 1 < exponentA n (fun i => (m i : ℝ)) →
        4 ≤ exponentA n (fun i => (m i : ℝ))) ∧
      ∃ m : Fin (n - 1) → ℤ, exponentA n (fun i => (m i : ℝ)) = 4) ∧
    (n = 3 →
      (∀ m : Fin (n - 1) → ℤ, 1 < exponentA n (fun i => (m i : ℝ)) →
        3 ≤ exponentA n (fun i => (m i : ℝ))) ∧
      ∃ m : Fin (n - 1) → ℤ, exponentA n (fun i => (m i : ℝ)) = 3) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P22

end
