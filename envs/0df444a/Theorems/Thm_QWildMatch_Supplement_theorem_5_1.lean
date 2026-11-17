-- Prove2me | Theorems.Thm_QWildMatch_Supplement_theorem_5_1
-- name    : QWildMatch.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:22:06.105098+00:00
-- url     : https://prove2.me/theorems/c1b5b078-f355-4be5-961a-5ac502342e34
-- title:
--   Theorem 5.1 — weighted-Hamming AP event bound: identity (1) and at most $1+q(2+V_\Gamma(A))$ regimes
-- statement:
--   Let $A=A[0]\cdots A[H-1]$ be a pattern over $\Sigma\cup\{\star\}$ and $\mu$ a substitution-cost function. Let $J$ be a set of text positions, $T$ a text and $B$ a reference with $B[x+p]=B[x]$ ($p\ge1$) on the coordinates read below, and let
--   $$E=\{e\in J: T[e]\ne B[e]\},\qquad |E|\le q .$$
--   Let $s_u=s_0+u\Gamma$ ($0\le u\le U$) with $\Gamma>0$, $p\mid\Gamma$, and every window $[s_u,s_u+H)$ contained in $J$. Write
--   $$D(u)=\sum_{r=0}^{H-1}\mu(A[r],T[s_u+r]),\qquad C=\sum_{r=0}^{H-1}\mu(A[r],B[s_0+r]),\qquad \Delta_e(r)=\mu(A[r],T[e])-\mu(A[r],B[e]).$$
--   Then
--
--   1. for every $0\le u\le U$,
--   $$D(u)=C+\sum_{e\in E\cap[s_u,s_u+H)}\Delta_e(e-s_u);\tag{1}$$
--   2. the sequence $D(0),\dots,D(U)$ has at most $1+q\,(2+V_\Gamma(A))$ consecutive maximal constant-value regimes;
--   3. in particular, if $V_\Gamma(A)=0$, it has at most $2q+1$ regimes.
--
--   Here $V_\Gamma(A)$ is the substitution-cost-row variation. The theorem says that, along one phase of an arithmetic progression of starts, the weighted Hamming cost is a background constant plus defect corrections and changes only at few events; this is what the event-counting argument of the paper exploits. Insertions and deletions are not allowed.
--
--   **Formalization Note** $\mu$ is arbitrary (no sign, no wildcard equation); $J$ need not be an interval; periodicity is assumed only on the hull $[s_0,s_U+H)$ of the windows.
--
--   Differences from the source:
--   - generalization: μ : (Σ ∪ {⋆}) × Σ → ℝ≥0 with μ(⋆, b) = 0, μ(a, a) = 0 (§3) → μ : Option Σ → Σ → ℝ arbitrary; reason: the theorem and its proof use no sign and no wildcard equation ('including when the wildcard locations are treated as exact symbols'); the §3 tables are special cases
--   - generalization: J an interval of text positions containing every window → J any set of integers containing every window; reason: the proof never uses that J is an interval once periodicity is stated on the hull of the windows; an interval is a special case
--   - reading: B[x + p] = B[x] on all relevant coordinates → B(x + p) = B(x) whenever s₀ ≤ x and x + p < s_U + H (the hull of the windows); reason: the relevant coordinates are those the windows read; this is the weakest such hypothesis, implied by periodicity on J
--   - encoding: positions, text T, reference B : ℤ → Σ, pattern A ∈ (Σ ∪ {⋆})^H → T, B : ℤ → Σ (only window positions are read); A : ℕ → Option Σ read at 0, …, H − 1; s_u = s₀ + uΓ with s₀ ∈ ℤ, Γ, p, U ∈ ℕ; reason: Lean representation; same instances
--   - encoding: |E| ≤ q → encard {e ∈ J : T e ≠ B e} ≤ q; reason: extended cardinality makes the bound also assert finiteness
--   - encoding: Σ over e ∈ E ∩ [s_u, s_u + H) of Δ_e(e − s_u) → sum over the finite set of e ∈ [s_u, s_u + H) with e ∈ J and T e ≠ B e of μ(A[e − s_u], T e) − μ(A[e − s_u], B e), the offset taken as a natural number; reason: Δ_e unfolded; e − s_u ≥ 0 on the window
--   - encoding: consecutive maximal constant-value regimes of D(0), …, D(U) → regimeCount D U = 1 + #{u < U : D(u + 1) ≠ D(u)}; reason: the number of maximal runs
--   - generalization: Σ a finite alphabet (§3) → Sym any type (no Fintype); reason: neither the identity (1) nor the regime count uses finiteness of the alphabet; a finite Σ is a special case
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu, Yue, Quantum Approximate Pattern Matching with Wildcards and Weighted Edits, STOC 2027 submission (file sha256 9e87a9dd…1f96), Theorem 5.1, p.7; setting §5, p.6

import Mathlib
import Definitions.Def_QWildMatch_Supplement_rowVariation
import Definitions.Def_QWildMatch_Supplement_regimeCount

namespace QWildMatch.Supplement

open Classical in
/-- Theorem 5.1 (Weighted-Hamming AP event bound), Zhao, Chen, Li, Kong, Peng, Yu, Yue, STOC 2027
submission (file sha256 9e87a9dd…), p.7, with the setting of §5, p.6: identity (1) for every `u`, the bound
`1 + q(2 + V_Γ(A))` on the constant regimes of `D(0), …, D(U)`, and `2q + 1` when `V_Γ(A) = 0`.

**Formalization Note** Positions are integers; the text `T` and the reference `B` are functions on `ℤ`, of
which only the windows are read. The windows are `[s_u, s_u + H)` with `s_u = s₀ + uΓ`, all inside `J`;
`J` is any set containing them. "`B[x + p] = B[x]` on all relevant coordinates" is read as periodicity on
the hull `[s₀, s_U + H)` of the windows. The defect set is `{e ∈ J : T e ≠ B e}`, of extended cardinality at
most `q` (so it is finite). `μ` is an arbitrary real function (no sign, no wildcard equation). In (1) the
sum over `e ∈ E ∩ [s_u, s_u + H)` has offset `e − s_u` as a natural number. -/
theorem theorem_5_1 {Sym : Type} (μ : Option Sym → Sym → ℝ) (H : ℕ) (A : ℕ → Option Sym)
    (J : Set ℤ) (T B : ℤ → Sym) (p : ℕ) (hp : 0 < p) (s₀ : ℤ) (Γ : ℕ) (hΓ : 0 < Γ)
    (hpΓ : p ∣ Γ) (U : ℕ)
    (hwin : ∀ u : ℕ, u ≤ U → ∀ r : ℕ, r < H → s₀ + (u : ℤ) * Γ + r ∈ J)
    (hB : ∀ x : ℤ, s₀ ≤ x → x + p < s₀ + (U : ℤ) * Γ + H → B (x + p) = B x)
    (q : ℕ) (hq : {e : ℤ | e ∈ J ∧ T e ≠ B e}.encard ≤ q) :
    (∀ u : ℕ, u ≤ U →
      ∑ r ∈ Finset.range H, μ (A r) (T (s₀ + (u : ℤ) * Γ + r)) =
        ∑ r ∈ Finset.range H, μ (A r) (B (s₀ + r)) +
        ∑ e ∈ (Finset.Ico (s₀ + (u : ℤ) * Γ) (s₀ + (u : ℤ) * Γ + H)).filter
            (fun e => e ∈ J ∧ T e ≠ B e),
          (μ (A (e - (s₀ + (u : ℤ) * Γ)).toNat) (T e) - μ (A (e - (s₀ + (u : ℤ) * Γ)).toNat) (B e))) ∧
    regimeCount (fun u => ∑ r ∈ Finset.range H, μ (A r) (T (s₀ + (u : ℤ) * Γ + r))) U ≤
      1 + q * (2 + rowVariation μ A H Γ) ∧
    (rowVariation μ A H Γ = 0 →
      regimeCount (fun u => ∑ r ∈ Finset.range H, μ (A r) (T (s₀ + (u : ℤ) * Γ + r))) U ≤
        2 * q + 1) := by sorry

end QWildMatch.Supplement
