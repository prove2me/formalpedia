-- Prove2me | Theorems.Thm_SpectralFeedback_reverse_paired_atoms_spectrum
-- name    : SpectralFeedback.reverse_paired_atoms_spectrum
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:28:31.47766+00:00
-- url     : https://prove2.me/theorems/c8428b35-ff02-42ce-8ec2-b960d461dc19
-- title:
--   Proof of Theorem H.2 — $T_\pm$ have spectra $c/2$ and sum to the active matrix
-- statement:
--   Let $s\ge1$, let $R\succeq0$ act on $\mathbb C^d$, and fix a decreasing spectral basis of $R$. Let $c$ be the paired spectrum and $T_\pm$ the reverse-paired atoms. Then:
--
--   1. the tail $\sum_{j>2s}\lambda_je_je_j^*$ is positive semidefinite;
--   2. $T_++T_-=R_{[\min(d,2s)]}$, the active matrix;
--   3. $(T_++\text{tail})+T_-=R$;
--   4. for each sign, $T_\pm\succeq0$, $\operatorname{rank}T_\pm\le s$, the $s$ largest eigenvalues of $T_\pm$ are the entries $c_1/2,\dots,c_s/2$ in some order, and all further eigenvalues of $T_\pm$ vanish.
--
--   For each sign the vectors $v_{i,\pm}$ have disjoint supports and squared norms $c_i/2$; this is the attainment half of Theorem H.2.
--
--   **Formalization Note** $T_\pm$ is `pairAtom R U s (±1)` for an arbitrary decreasing spectral basis `U`, $c$ is `pairedVec R s`, and eigenvalues are `eigDesc` (0-based, padded). A separate permutation is allowed for each sign.
--
--   Differences from the source:
--   - encoding: matrices on $\mathbb C^d$, eigenvalues $\lambda_i$ ($1$-based, padded by zeros) → `Matrix (Fin d) (Fin d) ℂ` for every `d : ℕ`; `eigDesc A (i-1)` (0-based, padded by zeros); reason: Lean indexing convention; same instances
--   - encoding: $T_\pm$ have nonzero spectra $c/2$, in some order → `∃ π : Equiv.Perm (Fin s), ∀ i, eigDesc T i = pairedVec R s (π i) / 2` and `eigDesc T i = 0` for `i ≥ s`; reason: the decreasing padded spectrum of $T_\pm$ is $c/2$ rearranged, followed by zeros; same content
--   - generalization: Hence $T_\pm$ have nonzero spectra $c/2$, in some order, and sum to the active matrix → adds the conjuncts $T_\pm\succeq0$, $\operatorname{rank}T_\pm\le s$, tail $\succeq0$ and $(T_++\text{tail})+T_-=R$; reason: these feasibility facts are used by the proof's next sentence (tail pooling) and hold for every input; dropping them gives the source's claim
-- source:
--   Qi, Spectral Structure and Exact Arithmetic of Finite-Feedback Measurement Discrimination, manuscript (Nov. 2026; PDF sha256 a5b5cf40…eabde9cf), proof of Theorem H.2, p.109 (PDF p.111); proof of Theorem F.4, p.94 (PDF p.96)

import Mathlib
import Definitions.Def_SpectralFeedback_pairAtom

open scoped ComplexOrder

namespace SpectralFeedback

/-- **Spectra of the reverse-paired atoms** (Qi, *Spectral Structure and Exact Arithmetic of
Finite-Feedback Measurement Discrimination*, manuscript (Nov. 2026), proof of Theorem H.2, p.109
(PDF p.111), last paragraph: "For each sign the displayed columns have disjoint supports and squared
norms `c_i/2`. Hence `T_±` have nonzero spectra `c/2`, in some order, and sum to the active matrix";
proof of Theorem F.4, p.94).

For `R ⪰ 0` and a decreasing spectral basis `U` of `R`: the tail beyond `2s` is positive
semidefinite; `T₊ + T₋` is the active matrix `R_{[min(d,2s)]}`; `(T₊ + tail) + T₋ = R`; and for
each sign `σ = ±1`, `T_σ ⪰ 0`, `rank T_σ ≤ s`, the `s` largest eigenvalues of `T_σ` are the entries
of `c/2` in some order, and all its further eigenvalues vanish.

**Formalization Note** `T_±` is `pairAtom R U s (±1)`; `c` is `pairedVec R s`; eigenvalues are
`eigDesc` (0-based, decreasing, padded by zeros). A separate permutation is allowed per sign. -/
theorem reverse_paired_atoms_spectrum (s : ℕ) (hs : 1 ≤ s) {d : ℕ}
    (R U : Matrix (Fin d) (Fin d) ℂ) (hR : R.PosSemidef) (hU : IsSortedEigenbasis R U) :
    (tailPart R U s).PosSemidef ∧
    pairAtom R U s 1 + pairAtom R U s (-1) = activePart R U (min d (2 * s)) ∧
    (pairAtom R U s 1 + tailPart R U s) + pairAtom R U s (-1) = R ∧
    ∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
      (pairAtom R U s σ).PosSemidef ∧ (pairAtom R U s σ).rank ≤ s ∧
      (∃ π : Equiv.Perm (Fin s),
        ∀ i : Fin s, eigDesc (pairAtom R U s σ) (i : ℕ) = pairedVec R s (π i) / 2) ∧
      ∀ i : ℕ, s ≤ i → eigDesc (pairAtom R U s σ) i = 0 := by sorry

end SpectralFeedback
