-- Prove2me | Theorems.Thm_SignFreeOracle_Separation_lemma_3_3
-- name    : SignFreeOracle.Separation.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:15:25.494149+00:00
-- url     : https://prove2.me/theorems/a5fdcb4f-ed57-4482-80e1-471b8f21b1af
-- title:
--   Lemma 3.3 (corrected: power-of-two degree normalization)
-- statement:
--   There is one uniform restricted circuit constructor, taking the bit length $m$ and degree bound $d$ as unary parameters, with resources polynomial in $m+d$, which receives an arbitrary normalized $m$-qubit complex witness $|\psi\rangle$ and accesses the Boolean encoding of any labelled graph of maximum degree at most $d$. If $D$ is the least power of two at least $\max(1,d)$, its acceptance is exactly
--   $$\frac12+\frac{\langle\psi|A_{G,\pi}|\psi\rangle}{2D}.$$
--   The family is chosen before the size, graph, labelling and witness. For $d=0$, $D=1$ and the graph is edgeless. For positive $d$, $d\le D<2d$. Power-of-two degree bounds recover the original identity. This is the exact spectral-verification interface for general sparse graphs; it does not restrict the witness to nonnegative amplitudes.
--
--   Differences from the source:
--   - generalization: sparse graphs with d polynomial in m → a universal constructor for every m and every natural d, with resource bound polynomial in m+d; reason: specializing to any polynomially bounded degree gives the original polynomial resource bound; all normalizers are exact
--   - correction: normalization by arbitrary d → normalization by the least power of two D at least max(1,d); reason: for m=2, one edge plus two isolates, d=3 and witness |0+>, the printed acceptance is 2/3, while this finite permutation gate set with zero/plus ancillas yields only dyadic probabilities
--   - encoding: finite graphs, labellings and quantum registers → finite vertex carriers, numerical labellings and complex amplitude functions; reason: these are equivalent finite representations; numerical neighbour positions are zero-based
-- source:
--   Hamoudi, Le Borgne, Teganahally Sridhara, Quantum Advantage with Sign-Free Proofs: An Oracle Separation between StoqMA and MA, STOC 2027 submission #601 (October 2026), Lemma 3.3, p. 9 (PDF p. 9)

import Definitions.Def_SignFreeOracle_Separation_Encoding

set_option autoImplicit false

namespace SignFreeOracle.Separation

open QAlgorithms.Complexity QAdvFew.PoQOracle

/-- Corrected power-of-two degree normalization; the printed identity can be nondyadic.
For d=3, one edge and witness |0+>, it predicts 2/3, impossible for this gate set. -/
theorem lemma_3_3 :
    ∃ (C : ∀ m, ℕ → StoqCircuit m) (size : Polynomial ℕ), UniformStoqParameters C ∧
      ∀ m d, (C m d).witness = m ∧
        m + (C m d).witness + (C m d).zeros + (C m d).plus ≤ size.eval (m + d) ∧
        (C m d).gates.length ≤ size.eval (m + d) ∧
        ∀ (G : SimpleGraph (Fin (2 ^ m))) (π : Equiv.Perm (Fin (2 ^ m))),
          maxDegree G ≤ d →
          ∀ (ψ : QState m), Normalized ψ →
            ∀ h : (C m d).witness = m,
            (C m d).accept (graphBits (d) G π) (fun _ => false)
              (fun z => ψ (fun i => z (Fin.cast h.symm i))) =
              1 / 2 + adjExpectation G π ψ / (2 * (degreeNormalization (d) : ℝ)) := by sorry

end SignFreeOracle.Separation
