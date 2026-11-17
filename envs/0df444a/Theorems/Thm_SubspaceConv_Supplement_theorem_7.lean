-- Prove2me | Theorems.Thm_SubspaceConv_Supplement_theorem_7
-- name    : SubspaceConv.Supplement.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:51:42.380552+00:00
-- url     : https://prove2.me/theorems/5e02dd19-471d-4a08-8754-263ec123af7e
-- title:
--   Theorem 7 — $\Omega_q(v\log v)$ bounded-coefficient gates for $I_{4r}^{r,3r}$ over $\mathbb C$, attained by Theorem 2
-- statement:
--   Let $r \ge 1$ and $v = |\mathrm{Gr}_q(4r, r)|$. Every linear circuit over $\mathbb C$ built from gates
--
--   $$z = \alpha x + \beta y, \qquad |\alpha|, |\beta| \le 1,$$
--
--   that applies the incidence transform $I_{4r}^{r,3r}$ (sums over the $r$-dimensional subspaces of each $3r$-dimensional subspace of $\mathbb F_q^{4r}$) has
--
--   $$\Omega_q(v \log v)$$
--
--   gates. The algorithm of Theorem 2 attains this bound up to a constant factor depending on $q$.
--
--   So Theorem 2 is optimal, up to a constant depending on $q$, in Morgenstern's bounded-coefficient model.
--
--   **Formalization Note** Circuits are `SubspaceConv.Supplement.BCCircuit` (free inputs; size = number of gates $\alpha x + \beta y$ with complex coefficients of modulus at most $1$). The statement has two clauses: a constant $c > 0$, depending only on the field, with size at least $c\, v \log v$ for every circuit computing $I_{4r}^{r,3r}$ on every input table and every $r \ge 1$; and a constant $C$ with a circuit of size at most $C\, v \log v$ for every $r \ge 1$. $\log$ is natural.
--
--   Differences from the source:
--   - encoding: the algorithm of theorem 2 attains this bound up to a constant factor → ∃ C, ∀ r ≥ 1, a well-formed bounded-coefficient circuit computing I_{4r}^{r,3r} of size ≤ C·v·log v; reason: the attainment clause states the existence of the circuit the algorithm yields; same content
-- source:
--   Perles, Weinstein, A Fast Algorithm for Subspace Convolution, STOC 2027 submission manuscript (sha256 a8ffb1b4e583122875209a3e25ee95aa3a7af933526e165d47c274634e604ab2), App. F, Theorem 7, p.26 (PDF p.27)

import Mathlib
import Definitions.Def_SubspaceConv_Supplement_Gr
import Definitions.Def_SubspaceConv_Supplement_incidence
import Definitions.Def_SubspaceConv_Supplement_BCCircuit

set_option autoImplicit false

namespace SubspaceConv.Supplement

/-- **Theorem 7**, Perles–Weinstein, *A Fast Algorithm for Subspace Convolution*, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), App. F, p.26 (PDF p.27). For `r ≥ 1` and `v = |Gr_q(4r, r)|`, applying
`I_{4r}^{r,3r}` over `C` requires `Ω_q(v log v)` gates of the form `z = αx + βy`, `|α|, |β| ≤ 1`.
The algorithm of theorem 2 attains this bound up to a constant factor depending on `q`.

**Formalization Note** Circuits are `SubspaceConv.Supplement.BCCircuit`: free input reads, gates
`α x_a + β x_b` with complex `|α|, |β| ≤ 1`, size = number of such gates. "Applying `I`" is computing
`I_{4r}^{r,3r} f` for every `f : Gr(4r, r) → ℂ`. Two clauses: a constant `c > 0`, depending only on
`F`, with `size ≥ c · v · log v` for every well-formed circuit that computes `I` (every `r ≥ 1`); and a
constant `C`, depending only on `F`, with a well-formed circuit of size at most `C · v · log v` for
every `r ≥ 1`. `log` is natural. -/
theorem theorem_7 (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    (∃ c : ℝ, 0 < c ∧ ∀ r : ℕ, 1 ≤ r →
      ∀ P : BCCircuit (Gr F (4 * r) r) (Gr F (4 * r) (3 * r)), P.WellFormed →
        (∀ f : Gr F (4 * r) r → ℂ, P.eval f = incidence r (3 * r) f) →
        c * (Fintype.card (Gr F (4 * r) r) : ℝ) * Real.log (Fintype.card (Gr F (4 * r) r) : ℝ)
          ≤ (P.size : ℝ)) ∧
    (∃ C : ℝ, ∀ r : ℕ, 1 ≤ r →
      ∃ P : BCCircuit (Gr F (4 * r) r) (Gr F (4 * r) (3 * r)), P.WellFormed ∧
        (∀ f : Gr F (4 * r) r → ℂ, P.eval f = incidence r (3 * r) f) ∧
        (P.size : ℝ) ≤
          C * (Fintype.card (Gr F (4 * r) r) : ℝ) * Real.log (Fintype.card (Gr F (4 * r) r) : ℝ)) := by sorry

end SubspaceConv.Supplement
