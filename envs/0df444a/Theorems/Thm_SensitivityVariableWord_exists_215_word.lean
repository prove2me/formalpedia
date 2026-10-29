-- Prove2me | Theorems.Thm_SensitivityVariableWord_exists_215_word
-- name    : SensitivityVariableWord.exists_215_word
-- status  : Open
-- author  : @dmilosch
-- created : 2026-10-28T23:51:54.526426+00:00
-- url     : https://prove2.me/theorems/b44a1e84-fdd6-4a5c-a770-91fc1133a055
-- title:
--   A variable-parameter canonical recipe word crosses the 2.15 threshold
-- statement:
--   Find a graph and labeling datum satisfying all the tournament, coherence, defect, and source bounds of the recursive-profile certificate interface, a positive number of states, and a nonempty admissible finite recipe word.
--
--   Starting from matrices equal to one on and above the diagonal and zero below it, compute the profile by the datum's transfer formulas and interval minima. If the datum has $K$ vertices, the word has length $L$, and its terminal height clamped below by two is $H$, require
--
--   $$H^{43}<K^{20L}.$$
--
--   The vertex count, outdegree, labeling, cutoffs, tolerance range, number of states, and recipes may all vary. There are no free profile matrices or return factors. The associated equivalence theorem identifies this with the general finite-certificate existence problem. This is the remaining open search problem: no crossing word, numerical parameter bound, or 2.15 separation is supplied or claimed to be known.
-- source:
--   Original parameter-free canonical-word reduction of SensitivityProfileCycle.Certificate and exists_215_certificate, https://prove2.me/theorems/6c031b2d-eb14-46d2-8d9e-f2db70527660. GraphData copies exactly the graph, labeling, and cutoff fields of https://prove2.me/definitions/6f70ee20-3318-4365-9377-022df0d68b3f. The step uses that module's rawZeroSourceCombined and rawOne without specializing any parameter. The interval envelope, unitProfile, and height come from SensitivityProfileSearch and SensitivityProfileWord; the fixed-parameter normalization theorem is https://prove2.me/theorems/ce0348ca-6a7e-4ada-a2fa-153d9cf45aa3. Underlying recursive bounds: accepted submission a9d25c46-43bd-4fb1-826b-0ed075b8cf0a at https://prove2.me/theorems/46659a00-722d-4dc9-b28e-ef02d6a0c9c2, by yousofy with Codex, retaining OpenAI/math, Robin Kothari with Codex, and earlier community attribution. No source is claimed to supply a witness reaching 2.15.

import Definitions.Def_SensitivityVariableWord

theorem SensitivityVariableWord.exists_215_word :
    ∃ (G : SensitivityVariableWord.GraphData) (n : ℕ)
      (word : List (SensitivityProfileCycle.Recipe (n + 1))),
      SensitivityVariableWord.Crosses215 G word := by sorry
