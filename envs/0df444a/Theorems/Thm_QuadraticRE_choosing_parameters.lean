-- Prove2me | Theorems.Thm_QuadraticRE_choosing_parameters
-- name    : QuadraticRE.choosing_parameters
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:14:31.72667+00:00
-- url     : https://prove2.me/theorems/8e722e87-7bfe-4bd4-b3f7-8dad52f7f263
-- title:
--   "Choosing the parameters" — $\delta_\lambda\le2^{-\lambda-2}$, $\varepsilon_\lambda\le\frac322^{-\lambda-2}$, sizes $O(\lambda^3)$
-- statement:
--   There are a universal constant $K$ and a polynomial $Q$ such that for every integer $\lambda\ge1$, with $j_\lambda,L_\lambda,h_\lambda$ as defined and $E_\lambda=E_{j_\lambda,h_\lambda}$:
--
--   1. $\delta_\lambda\le2^{-\lambda-2}$ and $\varepsilon_\lambda\le\tfrac32\,2^{-\lambda-2}$, where these are the actual errors of $E_\lambda$;
--   2. $(\log_25)\,2^{j_\lambda-4}\ge\lambda+2$, and $h_\lambda\ge3$;
--   3. $L_\lambda\le K\lambda^2$ and $h_\lambda\le K\lambda$;
--   4. the tape and the output of $E_\lambda$ have at most $K\lambda^3$ bits;
--   5. the encoder, the decoder and the simulator are computed by straight-line programs of at most $K\lambda^3$ gates;
--   6. $E_\lambda$ has a degree-two monomial description whose encoding has length at most $Q(\lambda)$.
--
--   This is the instantiation of the encoding of $abc+d$ that Lemma 4.11 and Theorem 4.12 use.
--
--   Differences from the source:
--   - reading: encoder, decoder and simulator run in time O(λ³) → straight-line programs of at most K·λ³ gates, one universal K; reason: the page derives the bound from the operation counts of Propositions 4.2 and 4.4; the page counts field operations and names no machine; an SLP pays for each operation and has no branching, so this is the strong reading (paper.md decision 3)
--   - reading: its expanded polynomial description has size polynomial in λ → a degree-two description expanding E_λ whose bit encoding has length at most Q(λ); reason: the size of a description is the length of its encoding
--   - encoding: δ_λ, ε_λ → the largest correctness error and the largest statistical distance of E_λ over the 16 inputs; reason: these are the errors the page bounds
--   - generalization: the displayed bounds → the displayed bounds and also h_λ ≥ 3; reason: an extra true conjunct that makes Propositions 4.3 and 4.4 applicable; the other conjuncts are the page's
-- source:
--   Orsini, Patra, From Degree Three to Degree Two: Statistical Randomized Encodings for All Functions, STOC 2027 submission manuscript (sha256 0c94deae…), §4.2.3, "Choosing the parameters", pp.28–29

import Mathlib
import Definitions.Def_QuadraticRE_jLam
import Definitions.Def_QuadraticRE_SLP
import Definitions.Def_QuadraticRE_PolyTimeFn

namespace QuadraticRE

/-- "Choosing the parameters", Orsini, Patra, *From Degree Three to Degree Two*, STOC 2027 submission manuscript (sha256 0c94deae…), §4.2.3, pp.28–29: the bounds on the actual errors `δ_λ`,
`ε_λ` of `E_λ`, and the `O(λ²)`, `O(λ)`, `O(λ³)` sizes.

**Formalization Note.** One universal `K` and one polynomial `Q`, chosen before `λ`. "Run in time
`O(λ³)`" is a straight-line program of that size; the page derives it from the operation counts of
Propositions 4.2 and 4.4. The clause `3 ≤ h_λ` makes those propositions applicable. -/
theorem choosing_parameters :
    ∃ (K : ℕ) (Q : Polynomial ℕ), ∀ lam : ℕ, 1 ≤ lam →
      deltaLam lam ≤ (1 / 2 : ℝ) ^ (lam + 2) ∧
      epsLam lam ≤ (3 / 2) * (1 / 2 : ℝ) ^ (lam + 2) ∧
      (lam : ℝ) + 2 ≤ Real.logb 2 5 * 2 ^ (jLam lam - 4) ∧
      3 ≤ hLam lam ∧
      LLam lam ≤ K * lam ^ 2 ∧
      hLam lam ≤ K * lam ∧
      rho (jLam lam) (hLam lam) ≤ K * lam ^ 3 ∧
      outLen (jLam lam) (hLam lam) ≤ K * lam ^ 3 ∧
      (∃ P : SLP (Fin 4 ⊕ Fin (rho (jLam lam) (hLam lam)))
          (Fin (4 ^ jLam lam) × Fin (hLam lam) × Fin 3),
        P.size ≤ K * lam ^ 3 ∧
        ∀ (x : Fin 4 → F2) (R : Tape (jLam lam) (hLam lam)) (t),
          P.eval (Sum.elim x R) t =
            encE (jLam lam) (hLam lam) (x 0) (x 1) (x 2) (x 3) R t.1 t.2.1 t.2.2) ∧
      (∃ P : SLP (Fin (4 ^ jLam lam) × Fin (hLam lam) × Fin 3) Unit,
        P.size ≤ K * lam ^ 3 ∧
        ∀ Z : Encoded (jLam lam) (hLam lam),
          P.eval (fun t => Z t.1 t.2.1 t.2.2) () = decE (jLam lam) (hLam lam) Z) ∧
      (∃ S : SLP (Unit ⊕ Fin (rho (jLam lam) (hLam lam)))
          (Fin (4 ^ jLam lam) × Fin (hLam lam) × Fin 3),
        S.size ≤ K * lam ^ 3 ∧
        ∀ (y : F2) (R : Tape (jLam lam) (hLam lam)) (t),
          S.eval (Sum.elim (fun _ => y) R) t =
            simE (jLam lam) (hLam lam) y R t.1 t.2.1 t.2.2) ∧
      (∃ D : Desc 4 (rho (jLam lam) (hLam lam)) (outLen (jLam lam) (hLam lam)),
        Expands D ∧ D.DegLE 2 ∧ (encDesc D).length ≤ Q.eval lam) := by sorry

end QuadraticRE
